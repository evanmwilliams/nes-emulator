use crate::opcodes;
use std::collections::HashMap;

bitflags! {
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIV           = 0b10000000;
    }
}

const STACK: u16 = 0x100;
const STACK_RESET: u8 = 0xfd;

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: CpuFlags,
    pub program_counter: u16,
    pub stack_pointer: u8,
    memory: [u8; 0xFFFF],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    IndirectX,
    IndirectY,
    NoneAddressing,
}

trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }
}

impl CPU {
    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            stack_pointer: STACK_RESET,
            status: CpuFlags::from_bits_truncate(0b100100),
            program_counter: 0,
            memory: [0; 0xFFFF],
        }
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,

            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,

            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),

            AddressingMode::ZeroPageX => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPageY => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }

            AddressingMode::AbsoluteX => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::AbsoluteY => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }

            AddressingMode::IndirectX => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::IndirectY => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }

            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        self.mem_read((STACK as u16) + self.stack_pointer as u16)
    }

    fn stack_push(&mut self, data: u8) {
        self.mem_write((STACK as u16) + self.stack_pointer as u16, data);
        self.stack_pointer = self.stack_pointer.wrapping_sub(1)
    }

    fn stack_push_u16(&mut self, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.stack_push(hi);
        self.stack_push(lo);
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lo = self.stack_pop() as u16;
        let hi = self.stack_pop() as u16;

        hi << 8 | lo
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let value = self.mem_read(addr);

        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x);
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        if result & 0b1000_0000 != 0 {
            self.status.insert(CpuFlags::NEGATIV);
        } else {
            self.status.remove(CpuFlags::NEGATIV);
        }
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.mem_write(addr, data.wrapping_add(1));
    }

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.mem_write(addr, data.wrapping_sub(1));
    }

    fn asl_accumulator(&mut self) {
        if self.register_a & 0b1000_0000 == 0b1000_0000 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        self.register_a = self.register_a << 1;

        self.update_zero_and_negative_flags(self.register_a);
    }

    fn asl(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);

        if data & 0b1000_0000 == 0b1000_0000 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        data = data << 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
    }

    fn lsr_accumulator(&mut self) {
        if self.register_a & 0b0000_0001 == 0b0000_0001 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        self.register_a = self.register_a >> 1;

        self.update_zero_and_negative_flags(self.register_a);
    }

    fn lsr(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);

        if data & 0b0000_0001 == 0b0000_0001 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        data = data >> 1;
        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
    }

    fn rol_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        data = data << 1;
        if old_carry {
            data = data | 1;
        }

        self.register_a = data;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn rol(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data >> 7 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        data = data << 1;
        if old_carry {
            data = data | 1;
        }

        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
    }

    fn ror_accumulator(&mut self) {
        let mut data = self.register_a;
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        data = data >> 1;
        if old_carry {
            data = data | 0b1000_0000;
        }

        self.register_a = data;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn ror(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let mut data = self.mem_read(addr);
        let old_carry = self.status.contains(CpuFlags::CARRY);

        if data & 1 == 1 {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        data = data >> 1;
        if old_carry {
            data = data | 0b1000_0000;
        }

        self.mem_write(addr, data);
        self.update_zero_and_negative_flags(data);
    }

    fn cmp(&mut self, mode: &AddressingMode, cmp_reg: u8) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);

        if data <= cmp_reg {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        self.update_zero_and_negative_flags(cmp_reg.wrapping_sub(data));
    }

    fn branch(&mut self, cond: bool) {
        if cond {
            let jump: i8 = self.mem_read(self.program_counter) as i8;
            let jump_addr = self
                .program_counter
                .wrapping_add(1)
                .wrapping_add(jump as u16);

            self.program_counter = jump_addr;
        }
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        let and = self.register_a & data;
        if and == 0 {
            self.status.insert(CpuFlags::ZERO);
        } else {
            self.status.remove(CpuFlags::ZERO);
        }

        self.status.set(CpuFlags::NEGATIV, data & 0b10000000 > 0);
        self.status.set(CpuFlags::OVERFLOW, data & 0b01000000 > 0);
    }

    // http://www.righto.com/2012/12/the-6502-overflow-flag-explained.html
    fn add_to_register_a(&mut self, data: u8) {
        let sum = self.register_a as u16
            + data as u16
            + (if self.status.contains(CpuFlags::CARRY) {
                1
            } else {
                0
            }) as u16;

        let carry = sum > 0xff;

        if carry {
            self.status.insert(CpuFlags::CARRY);
        } else {
            self.status.remove(CpuFlags::CARRY);
        }

        let result = sum as u8;

        if (data ^ result) & (result ^ self.register_a) & 0x80 != 0 {
            self.status.insert(CpuFlags::OVERFLOW);
        } else {
            self.status.remove(CpuFlags::OVERFLOW)
        }

        self.register_a = result;
        self.update_zero_and_negative_flags(result);
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(&mode);
        let data = self.mem_read(addr);
        self.add_to_register_a(((data as i8).wrapping_neg().wrapping_sub(1)) as u8);
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.add_to_register_a(value);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = self.register_a & value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = self.register_a ^ value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = self.register_a | value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn php(&mut self) {
        let mut flags = self.status.clone();
        flags.insert(CpuFlags::BREAK);
        flags.insert(CpuFlags::BREAK2);
        self.stack_push(flags.bits());
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.register_y = 0;
        self.stack_pointer = STACK_RESET;
        self.status = CpuFlags::from_bits_truncate(0b100100);

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn run(&mut self) {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;

        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes
                .get(&code)
                .expect(&format!("OpCode {:x} is not recognized", code));

            match code {
                // ARITHMETIC
                // ADC
                0x69 | 0x65 | 0x75 | 0x6d | 0x7d | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }

                // SBC
                0xe9 | 0xe5 | 0xf5 | 0xed | 0xfd | 0xf9 | 0xe1 | 0xf1 => {
                    self.sbc(&opcode.mode);
                }

                // AND
                0x29 | 0x25 | 0x35 | 0x2d | 0x3d | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }

                //EOR
                0x49 | 0x45 | 0x55 | 0x4d | 0x5d | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }

                // ORA
                0x09 | 0x05 | 0x15 | 0x0d | 0x1d | 0x19 | 0x01 | 0x11 => {
                    self.ora(&opcode.mode);
                }

                // STORES AND LOADS
                // LDA
                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }

                // LDX
                0xa2 | 0xa6 | 0xb6 | 0xae | 0xbe => {
                    self.ldx(&opcode.mode);
                }

                // LDY
                0xa0 | 0xa4 | 0xb4 | 0xac | 0xbc => {
                    self.ldy(&opcode.mode);
                }

                // STA
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }

                // STX
                0x86 | 0x96 | 0x8e => {
                    self.stx(&opcode.mode);
                }

                // STY
                0x84 | 0x94 | 0x8c => {
                    self.sty(&opcode.mode);
                }

                // SHIFTS
                // INX
                0xe8 => self.inx(),

                // INY
                0xc8 => self.iny(),

                // INC
                0xe6 | 0xf6 | 0xee | 0xfe => {
                    self.inc(&opcode.mode);
                }

                // DEX
                0xca => self.dex(),

                // DEY
                0x88 => self.dey(),

                // DEC
                0xc6 | 0xd6 | 0xce | 0xde => {
                    self.dec(&opcode.mode);
                }

                // ASL Accumulator
                0x0a => self.asl_accumulator(),

                // ASL
                0x06 | 0x16 | 0x0e | 0x1e => {
                    self.asl(&opcode.mode);
                }

                // LSR Accumulator
                0x4a => self.lsr_accumulator(),

                // LSR
                0x46 | 0x56 | 0x4e | 0x5e => {
                    self.lsr(&opcode.mode);
                }

                // ROL Accumulator
                0x2a => self.rol_accumulator(),

                // ROL
                0x26 | 0x36 | 0x2e | 0x3e => {
                    self.rol(&opcode.mode);
                }

                // ROR Accumulator
                0x6a => self.ror_accumulator(),

                // ROR
                0x66 | 0x76 | 0x6e | 0x7e => {
                    self.ror(&opcode.mode);
                }

                // CMP
                0xc9 | 0xc5 | 0xd5 | 0xcd | 0xdd | 0xd9 | 0xc1 | 0xd1 => {
                    self.cmp(&opcode.mode, self.register_a);
                }

                // CPX
                0xe0 | 0xe4 | 0xec => {
                    self.cmp(&opcode.mode, self.register_x);
                }

                // CPY
                0xc0 | 0xc4 | 0xcc => {
                    self.cmp(&opcode.mode, self.register_y);
                }

                // BRANCHING
                // JMP Immediate
                0x4c => {
                    let mem_addr = self.mem_read_u16(self.program_counter);
                    self.program_counter = mem_addr;
                }

                // JMP Indirect
                0x6c => {
                    let mem_address = self.mem_read_u16(self.program_counter);

                    let indirect_ref = if mem_address & 0x00FF == 0x00FF {
                        let lo = self.mem_read(mem_address);
                        let hi = self.mem_read(mem_address & 0xFF00);
                        (hi as u16) << 8 | (lo as u16)
                    } else {
                        self.mem_read_u16(mem_address)
                    };

                    self.program_counter = indirect_ref;
                }

                // JSR
                0x20 => {
                    self.stack_push_u16(self.program_counter + 2 - 1);
                    let target_address = self.mem_read_u16(self.program_counter);
                    self.program_counter = target_address;
                }

                // RTS
                0x60 => {
                    self.program_counter = self.stack_pop_u16() + 1;
                }

                // RTI
                0x40 => {
                    self.status.bits = self.stack_pop();
                    self.status.remove(CpuFlags::BREAK);
                    self.status.insert(CpuFlags::BREAK2);

                    self.program_counter = self.stack_pop_u16();
                }

                // BNE
                0xd0 => {
                    self.branch(!self.status.contains(CpuFlags::ZERO));
                }

                // BVS
                0x70 => {
                    self.branch(self.status.contains(CpuFlags::OVERFLOW));
                }

                // BVC
                0x50 => {
                    self.branch(!self.status.contains(CpuFlags::OVERFLOW));
                }

                // BPL
                0x10 => {
                    self.branch(!self.status.contains(CpuFlags::NEGATIV));
                }

                // BMI
                0x30 => {
                    self.branch(self.status.contains(CpuFlags::NEGATIV));
                }

                // BEQ
                0xf0 => {
                    self.branch(self.status.contains(CpuFlags::ZERO));
                }

                // BCS
                0xb0 => {
                    self.branch(self.status.contains(CpuFlags::CARRY));
                }

                // BCC
                0x90 => {
                    self.branch(!self.status.contains(CpuFlags::CARRY));
                }

                // BIT
                0x24 | 0x2c => {
                    self.bit(&opcode.mode);
                }

                // FLAGS CLEAR
                // CLD
                0xd8 => self.status.remove(CpuFlags::DECIMAL_MODE),

                // CLI
                0x58 => self.status.remove(CpuFlags::INTERRUPT_DISABLE),

                // CLV
                0xb8 => self.status.remove(CpuFlags::OVERFLOW),

                // CLC
                0x18 => self.status.remove(CpuFlags::CARRY),

                // SEC
                0x38 => self.status.insert(CpuFlags::CARRY),

                // SEI
                0x78 => self.status.insert(CpuFlags::INTERRUPT_DISABLE),

                // SED
                0xf8 => self.status.insert(CpuFlags::DECIMAL_MODE),

                // TAX
                0xaa => self.tax(),

                // TAY
                0xa8 => self.tay(),

                // TSX
                0xba => {
                    self.register_x = self.stack_pointer;
                    self.update_zero_and_negative_flags(self.register_x);
                }

                // TXA
                0x8a => {
                    self.register_a = self.register_x;
                    self.update_zero_and_negative_flags(self.register_a);
                }

                // TXS
                0x9a => {
                    self.stack_pointer = self.register_x;
                }

                // TYA
                0x98 => {
                    self.register_a = self.register_y;
                    self.update_zero_and_negative_flags(self.register_a);
                }

                // STACK
                // PHA
                0x48 => self.stack_push(self.register_a),

                // PLA
                0x68 => {
                    let data = self.stack_pop();
                    self.register_a = data;
                    self.update_zero_and_negative_flags(data);
                }

                // PHP
                0x08 => self.php(),

                // PLP
                0x28 => {
                    self.status.bits = self.stack_pop();
                    self.status.remove(CpuFlags::BREAK);
                    self.status.remove(CpuFlags::BREAK2);
                }

                // NOP
                0xea => {}

                // BRK
                0x00 => return,
                _ => todo!(),
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    // ARITHMETIC TESTS
    #[test]
    fn test_adc_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x69, 0xc4, 0x00]);

        assert_eq!(cpu.register_a, 0x84);
        assert_eq!(cpu.register_x, 0xc1);
    }

    #[test]
    fn test_sbc_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0xe9, 0xc4, 0x00]);

        assert_eq!(cpu.register_a, 0xfb);
        assert_eq!(cpu.register_x, 0xc1);
        assert!(cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_and_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc3, 0x29, 0xd2, 0x00]);
        assert_eq!(cpu.register_a, 0xc2);
        assert!(cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_eor_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc3, 0x49, 0xd2, 0x00]);
        assert_eq!(cpu.register_a, 0x11);
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_ora_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc3, 0x09, 0xd2, 0x00]);
        assert_eq!(cpu.register_a, 0xd3);
        assert!(cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    // STORES AND LOAD TESTS
    #[test]
    fn test_lda_immediate_load_data() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 5);
        assert!(cpu.status.bits() & 0b0000_0010 == 0);
        assert!(cpu.status.bits() & 0b1000_0000 == 0);
    }

    #[test]
    fn test_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status.bits() & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_lda_from_memory() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);

        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_ldx_immediate_load_data() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x05, 0x00]);
        assert_eq!(cpu.register_x, 5);
        assert!(cpu.status.bits() & 0b0000_0010 == 0);
        assert!(cpu.status.bits() & 0b1000_0000 == 0);
    }

    #[test]
    fn test_tax_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x0a, 0xaa, 0x00]);

        assert_eq!(cpu.register_x, 0x0a);
    }

    #[test]
    fn test_tay_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x0a, 0xa8, 0x00]);

        assert_eq!(cpu.register_y, 0x0a);
    }

    #[test]
    fn test_txa_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x80, 0x8a, 0x00]);

        assert_eq!(cpu.register_a, 0x80);
    }

    #[test]
    fn test_tya_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa0, 0x80, 0x98, 0x00]);

        assert_eq!(cpu.register_a, 0x80);
    }

    // SHIFT TESTS
    #[test]
    fn test_iny_overflow() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xc8, 0xe8, 0x00]);

        assert_eq!(cpu.register_y, 1)
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xff, 0xaa, 0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    fn test_inc_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xde, 0x85, 0x10, 0xe6, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0xdf);
    }

    #[test]
    fn test_dey_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa0, 0x80, 0x88, 0x00]);

        assert_eq!(cpu.register_y, 0x7f)
    }

    #[test]
    fn test_dex_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x80, 0xca, 0x00]);

        assert_eq!(cpu.register_x, 0x7f);
    }

    #[test]
    fn test_dec_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xde, 0x85, 0x10, 0xc6, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0xdd);
    }

    #[test]
    fn test_asl_accumulator_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x08, 0x0a, 0x00]);
        assert_eq!(cpu.register_a, 0x10);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_asl_accumulator_basic_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xa8, 0x0a, 0x00]);
        assert_eq!(cpu.register_a, 0x50);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_asl_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x08, 0x85, 0x10, 0x06, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x10);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_asl_basic_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xa8, 0x85, 0x10, 0x06, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x50);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_lsr_accumulator_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x10, 0x4a, 0x00]);
        assert_eq!(cpu.register_a, 0x08);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_lsr_accumulator_basic_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x50, 0x4a, 0x00]);
        assert_eq!(cpu.register_a, 0x28);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_lsr_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x10, 0x85, 0x10, 0x46, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x08);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_lsr_basic_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x50, 0x85, 0x10, 0x46, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x28);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_rol_accumulator_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x08, 0x2a, 0x00]);
        assert_eq!(cpu.register_a, 0x10);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_rol_accumulator_basic_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xa8, 0x2a, 0x00]);
        assert_eq!(cpu.register_a, 0x50);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_rol_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x08, 0x85, 0x10, 0x26, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x10);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_rol_basic_carry() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xa8, 0x85, 0x10, 0x26, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x50);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_ror_accumulator_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x10, 0x6a, 0x00]);
        assert_eq!(cpu.register_a, 0x08);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_ror_accumulator_basic_2() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x50, 0x6a, 0x00]);
        assert_eq!(cpu.register_a, 0x28);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_ror_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x10, 0x85, 0x10, 0x66, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x08);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_ror_basic_2() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x50, 0x85, 0x10, 0x66, 0x10, 0x00]);
        assert_eq!(cpu.memory[0x10], 0x28);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
        assert!(!cpu.status.contains(CpuFlags::ZERO));
    }

    #[test]
    fn test_cmp_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x10, 0x85, 0x10, 0xc5, 0x10, 0x00]);
        assert_eq!(cpu.register_a, 0x10);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_cpx_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa2, 0x10, 0x86, 0x10, 0xe0, 0x10, 0x00]);
        assert_eq!(cpu.register_x, 0x10);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
    }

    #[test]
    fn test_cpy_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa0, 0x10, 0x84, 0x10, 0xc0, 0x10, 0x00]);
        assert_eq!(cpu.register_y, 0x10);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(cpu.status.contains(CpuFlags::ZERO));
        assert!(!cpu.status.contains(CpuFlags::NEGATIV));
    }

    // AUXILLARY TESTS
    #[test]
    fn test_single_nop() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0xea, 0x00]);
        assert_eq!(cpu.register_a, 5);
        assert!(cpu.status.bits() & 0b0000_0010 == 0);
        assert!(cpu.status.bits() & 0b1000_0000 == 0);
    }

    #[test]
    fn test_interleaved_nops() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x05, 0xea, 0xea, 0xa9, 0x07, 0xea, 0xea, 0x00]);
        assert_eq!(cpu.register_a, 7);
        assert!(cpu.status.bits() & 0b0000_0010 == 0);
        assert!(cpu.status.bits() & 0b1000_0000 == 0);
    }

    #[test]
    fn test_bit_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0x85, 0x10, 0xa9, 0x00, 0x24, 0x10, 0x00]);
        assert!(cpu.status.contains(CpuFlags::OVERFLOW));
        assert!(!cpu.status.contains(CpuFlags::CARRY));
    }

    // BRANCHING TESTS
    #[test]
    fn test_jmp_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x08, 0x4c, 0x15]);
        assert_eq!(cpu.program_counter, 0x16);
    }

    #[test]
    fn test_jmp_indirect_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x08, 0x6c, 0xff]);
        assert_eq!(cpu.program_counter, 0x01);
    }

    #[test]
    fn test_jmp_label() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![
            0xa9, 0x03, 0x4c, 0x08, 0x06, 0x00, 0x00, 0x00, 0x8d, 0x00, 0x02,
        ]);
        assert_eq!(cpu.register_a, 0x03);
        assert_eq!(cpu.program_counter, 0x609);
    }

    #[test]
    fn test_bne_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![
            0xa2, 0x08, 0xca, 0x8e, 0x00, 0x02, 0xe0, 0x03, 0xd0, 0xf8, 0x8e, 0x01, 0x02, 0x00,
        ]);

        assert_eq!(cpu.register_x, 0x03);
        assert_eq!(cpu.program_counter, 0x800e);
    }

    // FLAG CLEAR TESTS
    #[test]
    fn test_clear_basic() {
        let mut cpu = CPU::new();
        cpu.status = CpuFlags::from_bits_truncate(0b111111);
        cpu.load_and_run(vec![0x18, 0xd8, 0x58, 0xb8, 0x00]);
        assert!(!cpu.status.contains(CpuFlags::CARRY));
        assert!(!cpu.status.contains(CpuFlags::DECIMAL_MODE));
        assert!(!cpu.status.contains(CpuFlags::INTERRUPT_DISABLE));
        assert!(!cpu.status.contains(CpuFlags::OVERFLOW));
    }

    #[test]
    fn test_set_basic() {
        let mut cpu = CPU::new();
        cpu.status = CpuFlags::from_bits_truncate(0b000000);
        cpu.load_and_run(vec![0x38, 0xf8, 0x78, 0x00]);
        assert!(cpu.status.contains(CpuFlags::CARRY));
        assert!(cpu.status.contains(CpuFlags::DECIMAL_MODE));
        assert!(cpu.status.contains(CpuFlags::INTERRUPT_DISABLE));
    }

    // STACK TESTS
    #[test]
    fn test_pha_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x80, 0x48, 0x00]);
        assert_eq!(cpu.stack_pop(), 0x80);
    }

    #[test]
    fn test_pla_basic() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0x80, 0x48, 0xa9, 0x00, 0x68, 0x00]);
        assert_eq!(cpu.register_a, 0x80)
    }

    // INTEGRATION TEST 
    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }
}
