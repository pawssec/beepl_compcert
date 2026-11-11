"""Typed map metadata checks and kernel state assertions; no map emulation."""
from kernel import Program

MAP_TYPES = {'xdp_map_counter': 6, 'xdp_map_bounds': 2, 'xdp_map_update': 1,
             'xdp_map_delete': 1, 'xdp_map_config': 2}


def validate_object(path, name):
    with Program(path, name, load=False) as program:
        info = program.map_info()
        expected = {'type': MAP_TYPES[name], 'key_size': 4, 'value_size': 8, 'max_entries': 1}
        for field, value in expected.items():
            if info[field] != value:
                raise AssertionError(f'BTF map {field}: expected {value}, got {info[field]}')
        return expected


def run_cases(program, name, packet, results):
    def check(label, retval, key, expected_value):
        actual, output, ns = program.run(packet)
        values = program.map_lookup(key)
        total = sum(values) if values is not None else None
        passed = actual == retval and output == packet and total == expected_value
        results.append({'case': label, 'actual': actual, 'expected': [retval],
                        'map_key': key, 'map_total': total, 'expected_map_total': expected_value,
                        'nonzero_cpu_values': {str(i): v for i, v in enumerate(values or []) if v},
                        'packet_preserved': output == packet, 'duration_ns': ns, 'passed': passed})
        print(f'{name} {label}: action={actual}, map[{key}]={total}; '
              f'{"PASS" if passed else "FAIL"}', flush=True)
        if not passed:
            raise AssertionError(f'{name}: unexpected action or map state in {label}')
    if name == 'xdp_map_counter':
        if sum(program.map_lookup(0)) != 0:
            raise AssertionError('New per-CPU counter must start at zero')
        for n in range(1, 6):
            check(f'packet_{n}', 2, 0, n)
    elif name == 'xdp_map_bounds':
        check('out_of_range_lookup_is_none', 2, 0, 0)
    elif name == 'xdp_map_update':
        if program.map_lookup(7) is not None:
            raise AssertionError('New hash map must be empty')
        check('insert_key', 2, 7, 42)
        program.map_update(7, 99)
        check('replace_key', 2, 7, 42)
    elif name == 'xdp_map_delete':
        check('delete_missing_key', 1, 7, None)
        program.map_update(7, 99)
        check('delete_existing_key', 2, 7, None)
        check('delete_again', 1, 7, None)
    elif name == 'xdp_map_config':
        for i, value in enumerate((0, 1, 0xffffffffffffffff, 0)):
            program.map_update(0, value)
            check(f'userspace_config_{i}', 2 if value == 0 else 1, 0, value)
    else:
        raise RuntimeError(f'No map tests for {name}')
