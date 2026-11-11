"""Small libbpf binding: test-run, map access and scoped raw-tracepoint attachment."""
import ctypes as C
import ctypes.util
import os
from contextlib import contextmanager


class TestRun(C.Structure):
    _fields_ = [('sz', C.c_size_t), ('data_in', C.c_void_p),
                ('data_out', C.c_void_p), ('data_size_in', C.c_uint32),
                ('data_size_out', C.c_uint32), ('ctx_in', C.c_void_p),
                ('ctx_out', C.c_void_p), ('ctx_size_in', C.c_uint32),
                ('ctx_size_out', C.c_uint32), ('retval', C.c_uint32),
                ('repeat', C.c_int), ('duration', C.c_uint32),
                ('flags', C.c_uint32), ('cpu', C.c_uint32),
                ('batch_size', C.c_uint32)]


class Program:
    def __init__(self, path, name, load=True):
        self.attachments = set()
        library = ctypes.util.find_library('bpf')
        if not library:
            raise RuntimeError('libbpf shared library is not installed')
        self.lib = C.CDLL(library, use_errno=True)
        for symbol, result, args in [
            ('bpf_object__open_file', C.c_void_p, [C.c_char_p, C.c_void_p]),
            ('libbpf_get_error', C.c_long, [C.c_void_p]),
            ('bpf_object__load', C.c_int, [C.c_void_p]),
            ('bpf_object__find_program_by_name', C.c_void_p, [C.c_void_p, C.c_char_p]),
            ('bpf_program__fd', C.c_int, [C.c_void_p]),
            ('bpf_object__close', None, [C.c_void_p]),
            ('bpf_prog_test_run_opts', C.c_int, [C.c_int, C.POINTER(TestRun)]),
            ('bpf_object__find_map_by_name', C.c_void_p, [C.c_void_p, C.c_char_p]),
            ('bpf_map__fd', C.c_int, [C.c_void_p]),
            ('bpf_map__type', C.c_uint32, [C.c_void_p]),
            ('bpf_map__key_size', C.c_uint32, [C.c_void_p]),
            ('bpf_map__value_size', C.c_uint32, [C.c_void_p]),
            ('bpf_map__max_entries', C.c_uint32, [C.c_void_p]),
            ('libbpf_num_possible_cpus', C.c_int, []),
            ('bpf_map_lookup_elem', C.c_int, [C.c_int, C.c_void_p, C.c_void_p]),
            ('bpf_map_update_elem', C.c_int, [C.c_int, C.c_void_p, C.c_void_p, C.c_uint64]),
            ('bpf_program__type', C.c_int, [C.c_void_p]),
            ('bpf_program__expected_attach_type', C.c_int, [C.c_void_p]),
            ('bpf_program__attach_cgroup', C.c_void_p, [C.c_void_p, C.c_int]),
            ('bpf_link__destroy', C.c_int, [C.c_void_p]),
            ('bpf_raw_tracepoint_open', C.c_int, [C.c_char_p, C.c_int]),
        ]:
            function = getattr(self.lib, symbol)
            function.restype, function.argtypes = result, args
        self.obj = self.lib.bpf_object__open_file(os.fsencode(path), None)
        err = self.lib.libbpf_get_error(self.obj)
        if not self.obj or err:
            self.obj = None
            raise OSError(-err if err else C.get_errno(), 'libbpf could not open object')
        try:
            result = self.lib.bpf_object__load(self.obj) if load else 0
            if result:
                raise OSError(-result, 'BPF load failed: ' + os.strerror(-result))
            program = self.lib.bpf_object__find_program_by_name(self.obj, name.encode())
            if not program:
                raise RuntimeError(f'Program {name!r} not found in object')
            self.program = program
            self.fd = self.lib.bpf_program__fd(program)
            if load and self.fd < 0:
                raise RuntimeError('Program has no loaded file descriptor')
        except BaseException:
            self.close()
            raise

    def map_info(self, name='counts'):
        handle = self.lib.bpf_object__find_map_by_name(self.obj, name.encode())
        if not handle:
            raise RuntimeError(f'Map {name!r} not found')
        return {field: getattr(self.lib, 'bpf_map__' + field)(handle)
                for field in ('fd', 'type', 'key_size', 'value_size', 'max_entries')}

    def map_slots(self, info):
        slots = self.lib.libbpf_num_possible_cpus() if info['type'] == 6 else 1
        if slots < 1 or info['key_size'] != 4 or info['value_size'] != 8:
            raise RuntimeError('Map reader requires uint32 keys and ulong values')
        return slots

    def map_lookup(self, key, name='counts'):
        info = self.map_info(name)
        values = (C.c_uint64 * self.map_slots(info))()
        k = C.c_uint32(key)
        result = self.lib.bpf_map_lookup_elem(info['fd'], C.byref(k), C.byref(values))
        if result:
            error = C.get_errno()
            if error == 2:
                return None
            raise OSError(error, 'Map lookup failed')
        return list(values)

    def map_update(self, key, value, name='counts'):
        info = self.map_info(name)
        slots = self.map_slots(info)
        values = (C.c_uint64 * slots)(*([value] * slots))
        k = C.c_uint32(key)
        if self.lib.bpf_map_update_elem(info['fd'], C.byref(k), C.byref(values), 0):
            raise OSError(C.get_errno(), 'Map update failed')

    def run(self, packet, context=None):
        source = C.create_string_buffer(packet)
        output = C.create_string_buffer(len(packet) + 256)
        opts = TestRun(sz=C.sizeof(TestRun), data_in=C.addressof(source),
                       data_out=C.addressof(output), data_size_in=len(packet),
                       data_size_out=C.sizeof(output), repeat=1)
        if context is not None:
            context_buffer = C.create_string_buffer(context)
            opts.ctx_in = C.addressof(context_buffer)
            opts.ctx_size_in = len(context)
        result = self.lib.bpf_prog_test_run_opts(self.fd, C.byref(opts))
        if result:
            raise OSError(-result, 'BPF_PROG_TEST_RUN failed: ' + os.strerror(-result))
        return opts.retval, output.raw[:opts.data_size_out], opts.duration

    @contextmanager
    def raw_tracepoint(self, name):
        fd = self.lib.bpf_raw_tracepoint_open(name.encode(), self.fd)
        if fd < 0:
            raise OSError(C.get_errno() or -fd, f'Cannot attach raw tracepoint {name}')
        self.attachments.add(fd)
        try:
            yield
        finally:
            if fd in self.attachments:
                self.attachments.remove(fd)
                os.close(fd)

    @contextmanager
    def cgroup(self, fd):
        link = self.lib.bpf_program__attach_cgroup(self.program, fd)
        err = self.lib.libbpf_get_error(link)
        if not link or err:
            raise OSError(-err if err else C.get_errno(), "Cannot attach cgroup program")
        try:
            yield
        finally:
            result = self.lib.bpf_link__destroy(link)
            if result:
                raise OSError(-result, "Cannot detach cgroup program")

    def close(self):
        for fd in list(self.attachments):
            self.attachments.remove(fd)
            os.close(fd)
        if self.obj:
            self.lib.bpf_object__close(self.obj)
            self.obj = None

    def __enter__(self):
        return self

    def __exit__(self, *unused):
        self.close()
