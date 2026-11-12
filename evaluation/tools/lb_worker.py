"""Namespace-local worker for load-balancer integration tests (invoked by lb-live)."""
import ctypes as C
import ctypes.util
import json
import socket
import sys


def main():
    mode = sys.argv[1]
    if mode == 'attach':
        class Hook(C.Structure):
            _fields_ = [('sz',C.c_size_t),('ifindex',C.c_int),('attach_point',C.c_int),('parent',C.c_uint32)]
        class Opts(C.Structure):
            _fields_ = [('sz',C.c_size_t),('prog_fd',C.c_int),('flags',C.c_uint32),('prog_id',C.c_uint32),('handle',C.c_uint32),('priority',C.c_uint32)]
        lib=C.CDLL(ctypes.util.find_library('bpf'),use_errno=True)
        lib.bpf_tc_attach.argtypes=[C.POINTER(Hook),C.POINTER(Opts)]
        lib.bpf_tc_attach.restype=C.c_int
        hook=Hook(sz=C.sizeof(Hook),ifindex=int(sys.argv[2]),attach_point=1)
        opts=Opts(sz=C.sizeof(Opts),prog_fd=int(sys.argv[3]),handle=1,priority=1)
        result=lib.bpf_tc_attach(C.byref(hook),C.byref(opts))
        if result: raise OSError(-result,'TC attach failed')
        print(json.dumps({'program_id':opts.prog_id,'attached':True}),flush=True)
        return
    if mode == 'server':
        label=sys.argv[2].encode()
        with socket.socket(socket.AF_INET,socket.SOCK_DGRAM) as sock:
            sock.bind(('192.0.2.100',9000))
            print(json.dumps({'ready':True}),flush=True)
            while True:
                data,peer=sock.recvfrom(4096)
                sock.sendto(label+b':'+data,peer)
    elif mode == 'client':
        with socket.socket(socket.AF_INET,socket.SOCK_DGRAM) as sock:
            sock.bind(('192.0.2.1',int(sys.argv[2])))
            sock.settimeout(0.5)
            print(json.dumps({'ready':True}),flush=True)
            for line in sys.stdin:
                payload=json.loads(line)['payload'].encode()
                try:
                    sock.sendto(payload,('192.0.2.100',9000))
                    data,peer=sock.recvfrom(4096)
                    result={'reply':data.decode(),'peer':list(peer)}
                except (socket.timeout,OSError) as error:
                    result={'reply':None,'error':str(error)}
                print(json.dumps(result),flush=True)
    else: raise ValueError(mode)


if __name__=='__main__': main()
