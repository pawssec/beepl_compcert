"""Strict, limited eBPF interpreter for evaluation smoke tests, NOT a verifier.

Only the instructions and three helper models used by this suite are implemented.
Unknown instructions, uninitialized reads, and accesses outside the supplied
context, packet, or stack fail. This cannot replace Linux verifier/kernel tests.
"""
import struct

MASK = (1 << 64) - 1


def xdp_section(path, section_name='xdp'):
    elf = path.read_bytes()
    offset = struct.unpack_from('<Q', elf, 40)[0]
    size, count, names_index = struct.unpack_from('<HHH', elf, 58)
    sections = [struct.unpack_from('<IIQQQQIIQQ', elf, offset + i * size) for i in range(count)]
    names = sections[names_index]
    strings = elf[names[4]:names[4] + names[5]]
    for section in sections:
        name = strings[section[0]:].split(b'\0', 1)[0]
        if name == section_name.encode():
            return elf[section[4]:section[4] + section[5]]
    raise RuntimeError(f'No {section_name} section')


def signed(value, bits):
    value &= (1 << bits) - 1
    return value - (1 << bits) if value & (1 << (bits - 1)) else value


def execute(code, packet, random_value=0, program_type='xdp', mark=0):
    context, data, stack = 0x10000, 0x20000, 0x30000
    ctx = struct.pack('<6I', data, data + len(packet), 0, 0, 0, 0)
    if program_type in ('socket', 'tc'):
        if len(packet) < 14:
            raise RuntimeError('Socket test-run requires an Ethernet header')
        pkt_type = 1 if packet[:6] == bytes([255]) * 6 else (2 if packet[0] & 1 else 3)
        ctx = struct.pack('<5I', len(packet) - (14 if program_type == 'socket' else 0),
                          pkt_type, mark, 0,
                          int.from_bytes(packet[12:14], 'little'))
    elif program_type != 'xdp':
        raise RuntimeError(f'Unsupported program type {program_type}')
    memory = dict(enumerate(ctx, context))
    memory.update(enumerate(packet, data))
    registers = [None] * 11
    registers[1], registers[10] = context, stack + 512
    pc, steps = 0, 0

    def reg(index):
        if index >= len(registers) or registers[index] is None:
            raise RuntimeError(f'Uninitialized register r{index} at instruction {pc}')
        return registers[index]

    def read(address, width):
        try:
            return int.from_bytes(bytes(memory[address + i] for i in range(width)), 'little')
        except KeyError as error:
            raise RuntimeError(f'Uninitialized/out-of-range memory read at instruction {pc}') from error

    while steps < 100000:
        if pc < 0 or 8 * (pc + 1) > len(code):
            raise RuntimeError('Instruction pointer outside program')
        op, regs, off, imm = struct.unpack_from('<BBhi', code, 8 * pc)
        dst, src = regs & 15, regs >> 4
        cls, operation = op & 7, op & 0xf0
        next_pc = pc + 1
        steps += 1
        if op == 0x18:
            _, _, _, high = struct.unpack_from('<BBhi', code, 8 * next_pc)
            if src:
                raise RuntimeError('Pseudo/map load not supported by smoke interpreter')
            registers[dst] = (imm & 0xffffffff) | ((high & 0xffffffff) << 32)
            next_pc += 1
        elif cls in (1, 2, 3) and op & 0xe0 == 0x60:
            width = {0: 4, 8: 2, 16: 1, 24: 8}[op & 0x18]
            if cls == 1:
                registers[dst] = read(reg(src) + off, width)
            else:
                address = reg(dst) + off
                if not stack <= address <= stack + 512 - width:
                    raise RuntimeError('Smoke interpreter permits stores only to stack')
                value = reg(src) if cls == 3 else imm
                memory.update(enumerate((value & ((1 << (8 * width)) - 1)).to_bytes(width, 'little'), address))
        elif cls in (4, 7):
            bits = 32 if cls == 4 else 64
            mask = (1 << bits) - 1
            rhs = (reg(src) if op & 8 else imm) & mask
            lhs = 0 if operation == 0xb0 else reg(dst) & mask
            if operation == 0x00: value = lhs + rhs
            elif operation == 0x10: value = lhs - rhs
            elif operation == 0x20: value = lhs * rhs
            elif operation == 0x30: value = lhs // rhs if rhs else 0
            elif operation == 0x40: value = lhs | rhs
            elif operation == 0x50: value = lhs & rhs
            elif operation == 0x60: value = lhs << (rhs & (bits - 1))
            elif operation == 0x70: value = lhs >> (rhs & (bits - 1))
            elif operation == 0x80: value = -lhs
            elif operation == 0x90: value = lhs % rhs if rhs else lhs
            elif operation == 0xa0: value = lhs ^ rhs
            elif operation == 0xb0: value = rhs
            elif operation == 0xc0: value = signed(lhs, bits) >> (rhs & (bits - 1))
            else: raise RuntimeError(f'Unsupported ALU opcode {op:#x}')
            if dst == 10:
                raise RuntimeError('Write to read-only stack pointer')
            registers[dst] = value & mask
        elif cls in (5, 6):
            if operation == 0x90:
                return reg(0) & 0xffffffff
            if operation == 0x80:
                if src or imm not in (5, 7, 32):
                    raise RuntimeError(f'Unsupported helper/subprogram call {imm}')
                if imm == 32:
                    if program_type != 'tc' or reg(1) != context:
                        raise RuntimeError('skb_change_type requires the TC context')
                    value = reg(2) & 0xffffffff
                    if value > 3 or read(context + 4, 4) > 3:
                        registers[0] = (-22) & MASK
                    else:
                        memory.update(enumerate(value.to_bytes(4, 'little'), context + 4))
                        registers[0] = 0
                else:
                    registers[0] = 1_000_000 if imm == 5 else random_value & 0xffffffff
                registers[1:6] = [None] * 5
            elif operation == 0x00:
                next_pc += off
            else:
                bits = 32 if cls == 6 else 64
                mask = (1 << bits) - 1
                lhs, rhs = reg(dst) & mask, (reg(src) if op & 8 else imm) & mask
                if operation == 0x10: condition = lhs == rhs
                elif operation == 0x20: condition = lhs > rhs
                elif operation == 0x30: condition = lhs >= rhs
                elif operation == 0x40: condition = bool(lhs & rhs)
                elif operation == 0x50: condition = lhs != rhs
                elif operation == 0x60: condition = signed(lhs, bits) > signed(rhs, bits)
                elif operation == 0x70: condition = signed(lhs, bits) >= signed(rhs, bits)
                elif operation == 0xa0: condition = lhs < rhs
                elif operation == 0xb0: condition = lhs <= rhs
                elif operation == 0xc0: condition = signed(lhs, bits) < signed(rhs, bits)
                elif operation == 0xd0: condition = signed(lhs, bits) <= signed(rhs, bits)
                else: raise RuntimeError(f'Unsupported jump opcode {op:#x}')
                if condition:
                    next_pc += off
        else:
            raise RuntimeError(f'Unsupported opcode {op:#x}')
        pc = next_pc
    raise RuntimeError('Smoke interpreter instruction budget exhausted')
