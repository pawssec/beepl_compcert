"""Two-backend UDP DSR integration test in four disposable network namespaces."""
import hashlib
import json
import os
import platform
import select
import shutil
import signal
import subprocess
import sys
import uuid
from datetime import datetime, timezone

from kernel import Program
from run import HERE, BUILD, prebuilt_program
from lb_eval import LB_NAME, VIP, PORT, MACS, configure, validate_object


def command(args, pass_fds=()):
    r=subprocess.run(args,text=True,capture_output=True,timeout=20,pass_fds=pass_fds)
    if r.returncode: raise RuntimeError(f'{args}: {r.stderr.strip()}')
    return r.stdout


def read_json(process):
    if not select.select([process.stdout],[],[],5)[0]:
        raise RuntimeError('Worker response timeout')
    line=process.stdout.readline()
    if not line: raise RuntimeError('Worker exited: '+process.stderr.read())
    return json.loads(line)


def main():
    suffix=uuid.uuid4().hex[:8]
    client,router,a,b=[f'beepl_lb_{n}_{suffix}' for n in ['c','r','a','b']]
    created=[]; children=[]
    report={'timestamp_utc':datetime.now(timezone.utc).isoformat(),'kernel':platform.release(),
            'program':LB_NAME,'tests':[],'passed':False,'cleanup_errors':[]}
    def interrupted(*unused): raise KeyboardInterrupt()
    signal.signal(signal.SIGTERM,interrupted)
    try:
        if os.geteuid()!=0: raise RuntimeError('Run sudo make -C evaluation/examples lb-live')
        for tool in ['ip','tc','sysctl']:
            if not shutil.which(tool): raise RuntimeError(f'Missing {tool}')
        source=HERE/'applications'/f'{LB_NAME}.bpl'; compiler=BUILD/'compiler/ccomp'
        obj=prebuilt_program(compiler,source,BUILD/'objects');validate_object(obj)
        for key,path in [('source_sha256',source),('object_sha256',obj),('compiler_sha256',compiler)]:
            report[key]=hashlib.sha256(path.read_bytes()).hexdigest()
        for ns in [client,router,a,b]:
            command(['ip','netns','add',ns]);created.append(ns)
            command(['ip','-n',ns,'link','set','dev','lo','up'])
        def nsrun(ns,args): return command(['ip','netns','exec',ns]+args)
        for dev,peer,subnet,mac_r,mac_p in [
            ('in0',client,'192.0.2','02:00:00:00:00:02','02:00:00:00:00:01'),
            ('outa',a,'192.0.3','02:00:00:00:00:10','02:00:00:00:00:11'),
            ('outb',b,'192.0.4','02:00:00:00:00:20','02:00:00:00:00:21')]:
            command(['ip','-n',router,'link','add','name',dev,'type','veth','peer','name','peer0'])
            command(['ip','-n',router,'link','set','dev','peer0','netns',peer])
            rlast,plast=(2,1) if peer==client else (1,2)
            for ns,device,address,mac in [(router,dev,f'{subnet}.{rlast}/30',mac_r),(peer,'peer0',f'{subnet}.{plast}/30',mac_p)]:
                command(['ip','-n',ns,'link','set','dev',device,'address',mac])
                command(['ip','-n',ns,'addr','add',address,'dev',device])
                command(['ip','-n',ns,'link','set','dev',device,'up'])
            for ns,device,remote,mac in [(router,dev,f'{subnet}.{plast}',mac_p),(peer,'peer0',f'{subnet}.{rlast}',mac_r)]:
                command(['ip','-n',ns,'neigh','replace',remote,'lladdr',mac,'nud','permanent','dev',device])
            if peer!=client:
                command(['ip','-n',peer,'addr','add',VIP+'/32','dev','lo'])
                command(['ip','-n',peer,'route','add','192.0.2.0/30','via',subnet+'.1'])
        command(['ip','-n',client,'route','add',VIP+'/32','via','192.0.2.2'])
        command(['ip','-n',router,'route','add','blackhole',VIP+'/32'])
        nsrun(router,['sysctl','-qw','net.ipv4.ip_forward=1'])
        for ns,devices in [(router,['all','default','in0','outa','outb']),(a,['all','default','peer0']),(b,['all','default','peer0'])]:
            for dev in devices:
                nsrun(ns,['sysctl','-qw',f'net.ipv4.conf.{dev}.rp_filter=0',f'net.ipv4.conf.{dev}.send_redirects=0'])
        worker=HERE/'tools/lb_worker.py'
        def spawn(ns,args):
            p=subprocess.Popen(['ip','netns','exec',ns,sys.executable,'-u',str(worker)]+args,
                               stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            children.append(p)
            if read_json(p)!={'ready':True}:raise RuntimeError('Worker not ready')
            return p
        spawn(a,['server','A']);spawn(b,['server','B'])
        clients=[spawn(client,['client',str(port)]) for port in [40000,40256]]
        def check(label,flow,backend):
            payload=f'{label}:{len(report["tests"])}'
            p=clients[flow];p.stdin.write(json.dumps({'payload':payload})+'\n');p.stdin.flush()
            actual=read_json(p)
            expected=None if backend is None else backend+':'+payload
            passed=actual['reply']==expected and (backend is None or actual.get('peer')==[VIP,PORT])
            report['tests'].append(dict(case=label,flow=flow,expected_backend=backend,actual=actual,passed=passed))
            print(f'{label}: {actual}; {"PASS" if passed else "FAIL"}',flush=True)
            if not passed:raise AssertionError(label+' unexpected backend reply')
        check('before_attach',0,None)
        tc=['ip','netns','exec',router,'tc']
        command(tc+['qdisc','add','dev','in0','clsact'])
        index=lambda dev:json.loads(command(['ip','-j','-n',router,'link','show','dev',dev]))[0]['ifindex']
        with Program(obj,LB_NAME) as program:
            configure(program,(index('outa'),index('outb')),MACS)
            report['attachment']=json.loads(command(['ip','netns','exec',router,sys.executable,str(worker),'attach',str(index('in0')),str(program.fd)],pass_fds=(program.fd,)))
            try:
                for repeat in range(3):
                    check(f'hash_a_{repeat}',0,'A');check(f'hash_b_{repeat}',1,'B')
                program.map_update(0,2);check('force_b_existing_flow',0,'B')
                program.map_update(0,1);check('force_a_existing_flow',1,'A')
                program.map_update(0,3);check('disabled_a',0,None);check('disabled_b',1,None)
                program.map_update(0,0);check('restore_hash_a',0,'A');check('restore_hash_b',1,'B')
                report['filter_stats']=json.loads(command(tc+['-s','-j','filter','show','dev','in0','ingress']))
            finally:
                command(tc+['filter','del','dev','in0','ingress','pref','1'])
            check('after_detach',0,None)
        report['passed']=True
    except (OSError,RuntimeError,AssertionError,ValueError,subprocess.TimeoutExpired,KeyboardInterrupt) as error:
        report['error']=str(error) or 'Interrupted';print(report['error'],file=sys.stderr)
    finally:
        for child in reversed(children):
            try:
                if child.poll() is None:child.terminate()
                try:child.wait(timeout=3)
                except subprocess.TimeoutExpired:child.kill();child.wait(timeout=3)
                for stream in [child.stdin,child.stdout,child.stderr]:stream.close()
            except (OSError,subprocess.TimeoutExpired) as error:report['cleanup_errors'].append(str(error))
        for ns in reversed(created):
            try:command(['ip','netns','del',ns])
            except (OSError,RuntimeError,subprocess.TimeoutExpired) as error:report['cleanup_errors'].append(str(error))
        report['cleanup_complete']=not report['cleanup_errors']
        if report['cleanup_errors']:report['passed']=False
        destination=HERE/'results/lb-live.json';destination.parent.mkdir(exist_ok=True)
        destination.write_text(json.dumps(report,indent=2)+'\n');print('Report:',destination)
    return 0 if report['passed'] else 1


if __name__=='__main__':sys.exit(main())
