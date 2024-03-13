fn div32(a: i32, b: i32) -> i32 {
    if b == 0 {
        -1
    } else if a == ((1 as i32) << (32 - 1)) && b == -1 {
        a
    } else {
        a / b
    }
}

fn divu32(a: u32, b: u32) -> u32 {
    if b == 0 {
        u32::MAX
    } else {
        return a / b;
    }
}

fn rem32(a: i32, b: i32) -> i32 {
    if b == 0 {
        a
    } else if a == (1 << (32 - 1)) && b == -1 {
        0
    } else {
        a % b
    }
}

fn remu32(a: u32, b: u32) -> u32 {
    if b == 0 {
        a
    } else {
        a % b
    }
}

fn div64(a: i64, b: i64) -> i64 {
    if b == 0 {
        return -1;
    } else if a == (1 << (64 - 1)) && b == -1 {
        return a;
    } else {
        return a / b;
    }
}
fn divu64(a: u64, b: u64) -> u64 {
    if b == 0 {
        return u64::MAX;
    } else {
        return a / b;
    }
}

fn rem64(a: i64, b: i64) -> i64 {
    if b == 0 {
        return a;
    } else if a == (1 << (64 - 1)) && b == -1 {
        return 0;
    } else {
        return a % b;
    }
}

fn remu64(a: u64, b: u64) -> u64 {
    if b == 0 {
        return a;
    } else {
        return a % b;
    }
}

fn mulh64(a: i64, b: i64) -> u64 {
    (((a as i128) * (b as i128)) >> 64) as u64
}

fn mulhsu64(a: i64, b: u64) -> u64 {
    (((a as i128) * (b as i128)) >> 64) as u64
}

fn mulhu64(a: u64, b: u64) -> u64 {
    (((a as i128) * (b as i128)) >> 64) as u64
}

fn sext(val: i32, n: i32) -> i32 {
    (val << (32 - n)) >> (32 - n)
}

fn get_field1(val: u32, src_pos: i32, dst_pos: i32, dst_pos_max: i32) -> u32 {
    let mask = ((1 << (dst_pos_max - dst_pos + 1)) - 1) << dst_pos;
    if dst_pos >= src_pos {
        (val << (dst_pos - src_pos)) & mask
    } else {
        (val >> (src_pos - dst_pos)) & mask
    }
}
#[derive(PartialEq)]
pub enum Exception {
    OK = -1,
    IllegalInstruction = 2,
    BREAKPOINT = 3,
    LoadAccessFault = 5,
    StoreAccessFault = 7,
    NotCompress = 8,
    Ecall = 9,
}

pub struct Cpu {
    pub reg: [u64; 32],
    pub fp_reg: [u64; 32],
    pub fs: u8,
    pub pc: u64,
    //  csrs: [u8; 4096],
    //  enable_paging: bool,
    // pagetable: u64,
    reservation_set: Vec<u64>,
    pub code: Vec<u8>,
    pub code_ptr: usize,
    pub max_code_len: usize,
}

/*

31 27 26 25    24  20   19   15   14  12   11  7        6    0
funct7       |  rs2   |  rs1    | funct3 | rd         |   opcode   R-type
imm[11:0]             |  rs1    | funct3 | rd         |   opcode   I-type
imm[11:5]    |  rs2   |  rs1    | funct3 |imm[4:0]    |   opcode   S-type
imm[12|10:5] |  rs2   |  rs1    | funct3 |imm[4:1|11] |   opcode   B-type
imm[31:12]                               | rd         |   opcode   U-type
imm[20|10:1|11|19:12]                    | rd         |   opcode   J-type

RV32I Base Instruction Set
imm[31:12]                               |  rd        |     0110111            LUI
imm[31:12]                               |  rd        |     0010111            AUIPC
imm[20|10:1|11|19:12]                    |  rd        |     1101111            JAL
imm[11:0]            |    rs1   |  000   |  rd        |     1100111            JALR
imm[12|10:5] rs2 rs1 000 imm[4:1|11] 1100011 BEQ
imm[12|10:5] rs2 rs1 001 imm[4:1|11] 1100011 BNE
imm[12|10:5] rs2 rs1 100 imm[4:1|11] 1100011 BLT
imm[12|10:5] rs2 rs1 101 imm[4:1|11] 1100011 BGE
imm[12|10:5] rs2 rs1 110 imm[4:1|11] 1100011 BLTU
imm[12|10:5] rs2 rs1 111 imm[4:1|11] 1100011 BGEU
imm[11:0] rs1 000 rd 0000011                 LB
imm[11:0] rs1 001 rd 0000011                 LH
imm[11:0] rs1 010 rd 0000011                 LW
imm[11:0] rs1 100 rd 0000011                 LBU
imm[11:0] rs1 101 rd 0000011                 LHU
imm[11:5] rs2 rs1 000 imm[4:0] 0100011       SB
imm[11:5] rs2 rs1 001 imm[4:0] 0100011       SH
imm[11:5] rs2 rs1 010 imm[4:0] 0100011       SW
imm[11:0] rs1 000 rd 0010011                 ADDI
imm[11:0] rs1 010 rd 0010011                 SLTI
imm[11:0] rs1 011 rd 0010011                 SLTIU
imm[11:0] rs1 100 rd 0010011                 XORI
imm[11:0] rs1 110 rd 0010011                 ORI
imm[11:0] rs1 111 rd 0010011                 ANDI
0000000 shamt rs1 001 rd 0010011             SLLI
0000000 shamt rs1 101 rd 0010011             SRLI
0100000 shamt rs1 101 rd 0010011             SRAI
0000000 rs2 rs1 000 rd 0110011               ADD
0100000 rs2 rs1 000 rd 0110011               SUB
0000000 rs2 rs1 001 rd 0110011               SLL
0000000 rs2 rs1 010 rd 0110011               SLT
0000000 rs2 rs1 011 rd 0110011               SLTU
0000000 rs2 rs1 100 rd 0110011               XOR
0000000 rs2 rs1 101 rd 0110011               SRL
0100000 rs2 rs1 101 rd 0110011               SRA
0000000 rs2 rs1 110 rd 0110011               OR
0000000 rs2 rs1 111 rd 0110011               AND
fm pred succ rs1 000 rd 0001111              FENCE
imm[11:0] rs1 001 rd 0001111                 FENCE.I
000000000000 00000 000 00000 1110011         ECALL
000000000001 00000 000 00000 1110011         EBREAK
csr rs1 001 rd 1110011                       CSRRW
csr rs1 010 rd 1110011                       CSRRS
csr rs1 011 rd 1110011                       CSRRC
csr uimm 101 rd 1110011                      CSRRWI
csr uimm 110 rd 1110011                      CSRRSI
csr uimm 111 rd 1110011                      CSRRCI

RV64I Base Instruction Set (in addition to RV32I)
imm[11:0] rs1 110 rd 0000011                 LWU
imm[11:0] rs1 011 rd 0000011                 LD
imm[11:5] rs2 rs1 011 imm[4:0] 0100011       SD
000000 shamt rs1 001 rd 0010011              SLLI
000000 shamt rs1 101 rd 0010011              SRLI
010000 shamt rs1 101 rd 0010011              SRAI
imm[11:0] rs1 000 rd 0011011                 ADDIW
0000000 shamt rs1 001 rd 0011011             SLLIW
0000000 shamt rs1 101 rd 0011011             SRLIW
0100000 shamt rs1 101 rd 0011011             SRAIW
0000000 rs2 rs1 000 rd 0111011               ADDW
0100000 rs2 rs1 000 rd 0111011               SUBW
0000000 rs2 rs1 001 rd 0111011               SLLW
0000000 rs2 rs1 101 rd 0111011               SRLW
0100000 rs2 rs1 101 rd 0111011               SRAW



RV32M Standard Extension
0000001 rs2 rs1 000 rd 0110011              MUL
0000001 rs2 rs1 001 rd 0110011              MULH
0000001 rs2 rs1 010 rd 0110011              MULHSU
0000001 rs2 rs1 011 rd 0110011              MULHU
0000001 rs2 rs1 100 rd 0110011              DIV
0000001 rs2 rs1 101 rd 0110011              DIVU
0000001 rs2 rs1 110 rd 0110011              REM
0000001 rs2 rs1 111 rd 0110011              REMU

RV64M Standard Extension (in addition to RV32M)
0000001 rs2 rs1 000 rd 0111011              MULW
0000001 rs2 rs1 100 rd 0111011              DIVW
0000001 rs2 rs1 101 rd 0111011              DIVUW
0000001 rs2 rs1 110 rd 0111011              REMW
0000001 rs2 rs1 111 rd 0111011              REMUW

RV32A Standard Extension
00010 aq rl 00000 rs1 010 rd 0101111 LR.W
00011 aq rl rs2 rs1 010 rd 0101111 SC.W
00001 aq rl rs2 rs1 010 rd 0101111 AMOSWAP.W
00000 aq rl rs2 rs1 010 rd 0101111 AMOADD.W
00100 aq rl rs2 rs1 010 rd 0101111 AMOXOR.W
01100 aq rl rs2 rs1 010 rd 0101111 AMOAND.W
01000 aq rl rs2 rs1 010 rd 0101111 AMOOR.W
10000 aq rl rs2 rs1 010 rd 0101111 AMOMIN.W
10100 aq rl rs2 rs1 010 rd 0101111 AMOMAX.W
11000 aq rl rs2 rs1 010 rd 0101111 AMOMINU.W
11100 aq rl rs2 rs1 010 rd 0101111 AMOMAXU.W

RV64A Standard Extension (in addition to RV32A)
00010 aq rl 00000 rs1 011 rd 0101111 LR.D
00011 aq rl rs2 rs1 011 rd 0101111 SC.D
00001 aq rl rs2 rs1 011 rd 0101111 AMOSWAP.D
00000 aq rl rs2 rs1 011 rd 0101111 AMOADD.D
00100 aq rl rs2 rs1 011 rd 0101111 AMOXOR.D
01100 aq rl rs2 rs1 011 rd 0101111 AMOAND.D
01000 aq rl rs2 rs1 011 rd 0101111 AMOOR.D
10000 aq rl rs2 rs1 011 rd 0101111 AMOMIN.D
10100 aq rl rs2 rs1 011 rd 0101111 AMOMAX.D
11000 aq rl rs2 rs1 011 rd 0101111 AMOMINU.D
11100 aq rl rs2 rs1 011 rd 0101111 AMOMAXU.D

*/

/*
regs
x0       zero
x1/ra    return address
x2/sp    stack pointer
x3/gp    global pointer
x4/tp    thread pointer
x5/t0    temp
x6/t1    temp
x7/t2    temp
x8/s0/fp saved register frame pointer
x9/s1    saved register
x10/a0   func arg  ,return value
x11/a1   func arg  ,return value
x12/a2   func arg
x13/a3   func arg
x14/a4   func arg
x15/a5   func arg
x16/a6   func arg
x17/a7   func arg
x18/s2   saved register
x19/s3   saved register
x20/s4   saved register
x21/s5   saved register
x22/s6   saved register
x23/s7   saved register
x24/s8   saved register
x25/s9   saved register
x26/s10  saved register
x27/s11  saved register
x28/t3   temp
x29/t4   temp
x30/t5   temp
x31/t6   temp
 */
impl Cpu {
    pub fn new() -> Cpu {
        Cpu {
            reg: [0; 32],
            fp_reg: [0; 32],
            fs: 0,
            pc: 0,
            // csrs: [0; 4096],
            // enable_paging: false,
            // pagetable: 0,
            reservation_set: Vec::new(),
            code: Vec::new(),
            code_ptr: 0,
            max_code_len: 0,
        }
    }

    fn target_read_u8(&mut self, rval: &mut u8, addr: usize) -> i32 {
        *rval = self.code[addr];

        0
    }
    fn target_read_u16(&mut self, rval: &mut u16, addr: usize) -> i32 {
        *rval = u16::from_le_bytes(self.code[addr..addr + 2].try_into().unwrap());
        0
    }
    fn target_read_u32(&mut self, rval: &mut u32, addr: usize) -> i32 {
        *rval = u32::from_le_bytes(self.code[addr..addr + 4].try_into().unwrap());

        0
    }
    fn target_read_u64(&mut self, rval: &mut u64, addr: usize) -> i32 {
        *rval = u64::from_le_bytes(self.code[addr..addr + 8].try_into().unwrap());

        0
    }

    fn target_write_u8(&mut self, value: u8, addr: usize) -> i32 {
        self.code[addr] = value;

        0
    }
    fn target_write_u16(&mut self, value: u16, addr: usize) -> i32 {
        self.code[addr..addr + 2].copy_from_slice(value.to_le_bytes().as_slice());

        return 0;
    }
    fn target_write_u32(&mut self, value: u32, addr: usize) -> i32 {
        self.code[addr..addr + 4].copy_from_slice(value.to_le_bytes().as_slice());

        return 0;
    }
    fn target_write_u64(&mut self, value: u64, addr: usize) -> i32 {
        self.code[addr..addr + 8].copy_from_slice(value.to_le_bytes().as_slice());

        return 0;
    }

    pub fn cpu_fetch_ins(&mut self) -> u32 {
        let idx = self.pc as usize;
        u32::from_le_bytes(self.code[idx..idx + 4].try_into().unwrap())
    }

    fn cpu_execute_compress(&mut self, insn: u32, opcode: u32, rd: usize) -> Exception {
        //  let opcode = insn & 0x7f;

        match opcode {
            0 | 4 | 8 | 12 | 16 | 20 | 24 | 28 | 32 | 36 | 40 | 44 | 48 | 52 | 56 | 60 | 64
            | 68 | 72 | 76 | 80 | 84 | 88 | 92 | 96 | 100 | 104 | 108 | 112 | 116 | 120 | 124 => {
                let funct3 = (insn >> 13) & 7;
                let rd = (((insn >> 2) & 7) | 8) as usize;
                match funct3 {
                    0 => {
                        /* c.addi4spn */
                        let imm = get_field1(insn, 11, 4, 5)
                            | get_field1(insn, 7, 6, 9)
                            | get_field1(insn, 6, 2, 2)
                            | get_field1(insn, 5, 3, 3);
                        if imm == 0 {
                            return Exception::IllegalInstruction;
                        }
                        //println!{"shit addi {} {:X} {:X} {:X}\n",rd,self.reg[2],imm,insn};
                        self.reg[rd] = self.reg[2] + imm as i32 as u64;
                    }
                    1 => {
                        /* c.fld */
                        let imm = get_field1(insn, 10, 3, 5) | get_field1(insn, 5, 6, 7);
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let addr = self.reg[rs1 as usize] + imm as i32 as u64;
                        let mut rval = 0;
                        if self.target_read_u64(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        self.fp_reg[rd] = rval;
                        self.fs = 3;
                    }
                    2 => {
                        /* c.lw */
                        let imm = get_field1(insn, 10, 3, 5)
                            | get_field1(insn, 6, 2, 2)
                            | get_field1(insn, 5, 6, 6);
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let addr = self.reg[rs1 as usize] + imm as i32 as u64;
                        let mut rval = 0;
                        if self.target_read_u32(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as i32 as u64;
                        }
                    }
                    3 => {
                        /* c.ld */
                        let imm = get_field1(insn, 10, 3, 5) | get_field1(insn, 5, 6, 7);
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let addr = self.reg[rs1 as usize] + imm as i32 as u64;
                        let mut rval = 0;
                        if self.target_read_u64(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval;
                        }
                    }
                    5 => {
                        /* c.fsd */
                        let imm = get_field1(insn, 10, 3, 5) | get_field1(insn, 5, 6, 7);
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let addr = self.reg[rs1 as usize] + imm as i32 as u64;
                        if self.target_write_u64(self.fp_reg[rd], addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    6 => {
                        /* c.sw */
                        let imm = get_field1(insn, 10, 3, 5)
                            | get_field1(insn, 6, 2, 2)
                            | get_field1(insn, 5, 6, 6);
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let addr = self.reg[rs1 as usize] + imm as i32 as u64;
                        if self.target_write_u32(self.reg[rd] as u32, addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    7 => {
                        /* c.sd */
                        let imm = get_field1(insn, 10, 3, 5) | get_field1(insn, 5, 6, 7);
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let addr = self.reg[rs1 as usize] + imm as i32 as u64;
                        if self.target_write_u64(self.reg[rd], addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                self.pc += 2;
            }
            1 | 5 | 9 | 13 | 17 | 21 | 25 | 29 | 33 | 37 | 41 | 45 | 49 | 53 | 57 | 61 | 65
            | 69 | 73 | 77 | 81 | 85 | 89 | 93 | 97 | 101 | 105 | 109 | 113 | 117 | 121 | 125 => {
                let funct3 = (insn >> 13) & 7;
                match funct3 {
                    0 => {
                        /* c.addi/c.nop */
                        if rd != 0 {
                            let imm = sext(
                                (get_field1(insn, 12, 5, 5) | get_field1(insn, 2, 0, 4)) as i32,
                                6,
                            );
                            self.reg[rd] = self.reg[rd] + imm as u64;
                        }
                    }
                    1 => {
                        /* c.addiw */
                        if rd != 0 {
                            let imm = sext(
                                (get_field1(insn, 12, 5, 5) | get_field1(insn, 2, 0, 4)) as i32,
                                6,
                            );
                            self.reg[rd] = (self.reg[rd] + imm as u64) as i32 as u64;
                        }
                    }
                    2 => {
                        //* c.li */
                        if rd != 0 {
                            let imm = sext(
                                (get_field1(insn, 12, 5, 5) | get_field1(insn, 2, 0, 4)) as i32,
                                6,
                            );
                            self.reg[rd] = imm as u64;
                        }
                    }
                    3 => {
                        if rd == 2 {
                            /* c.addi16sp */
                            let imm = sext(
                                (get_field1(insn, 12, 9, 9)
                                    | get_field1(insn, 6, 4, 4)
                                    | get_field1(insn, 5, 6, 6)
                                    | get_field1(insn, 3, 7, 8)
                                    | get_field1(insn, 2, 5, 5))
                                    as i32,
                                10,
                            );

                            self.reg[2] = self.reg[2] + imm as u64;
                        } else if rd != 0 {
                            /* c.lui */
                            let imm = sext(
                                (get_field1(insn, 12, 17, 17) | get_field1(insn, 2, 12, 16)) as i32,
                                18,
                            );
                            self.reg[rd] = imm as u64;
                        }
                    }
                    4 => {
                        let funct3 = (insn >> 10) & 3;
                        let rd: usize = (((insn >> 7) & 7) | 8) as usize;
                        match funct3 {
                            0 | 1 => {
                                let imm = get_field1(insn, 12, 5, 5) | get_field1(insn, 2, 0, 4);
                                if funct3 == 0 {
                                    /* c.srli */
                                    self.reg[rd] = self.reg[rd] >> imm;
                                } else {
                                    /* c.srai */
                                    self.reg[rd] = ((self.reg[rd] as i64) >> imm) as u64;
                                }
                            }
                            2 => {
                                /* c.andi */
                                let imm = sext(
                                    (get_field1(insn, 12, 5, 5) | get_field1(insn, 2, 0, 4)) as i32,
                                    6,
                                );
                                self.reg[rd] = self.reg[rd] & imm as u64;
                            }
                            3 => {
                                let rs2 = (((insn >> 2) & 7) | 8) as usize;
                                let funct3 = ((insn >> 5) & 3) | ((insn >> (12 - 2)) & 4);
                                match funct3 {
                                    0 => {
                                        /* c.sub */
                                        self.reg[rd] = self.reg[rd] - self.reg[rs2];
                                    }
                                    1 => {
                                        /* c.xor */
                                        self.reg[rd] = self.reg[rd] ^ self.reg[rs2];
                                    }
                                    2 => {
                                        /* c.or */
                                        self.reg[rd] = self.reg[rd] | self.reg[rs2];
                                    }
                                    3 => {
                                        /* c.and */
                                        self.reg[rd] = self.reg[rd] & self.reg[rs2];
                                    }
                                    4 => {
                                        /* c.subw */
                                        self.reg[rd] = (self.reg[rd] - self.reg[rs2]) as i32 as u64;
                                    }
                                    5 => {
                                        /* c.addw */
                                        self.reg[rd] = (self.reg[rd] + self.reg[rs2]) as i32 as u64;
                                    }
                                    _ => {
                                        return Exception::IllegalInstruction;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    5 => {
                        /* c.j */
                        let imm = sext(
                            (get_field1(insn, 12, 11, 11)
                                | get_field1(insn, 11, 4, 4)
                                | get_field1(insn, 9, 8, 9)
                                | get_field1(insn, 8, 10, 10)
                                | get_field1(insn, 7, 6, 6)
                                | get_field1(insn, 6, 7, 7)
                                | get_field1(insn, 3, 1, 3)
                                | get_field1(insn, 2, 5, 5)) as i32,
                            12,
                        );
                        self.pc = self.pc + imm as u64;
                        return Exception::OK;
                    }
                    6 => {
                        /* c.beqz */
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let imm = sext(
                            (get_field1(insn, 12, 8, 8)
                                | get_field1(insn, 10, 3, 4)
                                | get_field1(insn, 5, 6, 7)
                                | get_field1(insn, 3, 1, 2)
                                | get_field1(insn, 2, 5, 5)) as i32,
                            9,
                        );
                        if self.reg[rs1 as usize] == 0 {
                            self.pc = self.pc + imm as u64;
                            return Exception::OK;
                        }
                    }
                    7 => {
                        /* c.bnez */
                        let rs1 = ((insn >> 7) & 7) | 8;
                        let imm = sext(
                            (get_field1(insn, 12, 8, 8)
                                | get_field1(insn, 10, 3, 4)
                                | get_field1(insn, 5, 6, 7)
                                | get_field1(insn, 3, 1, 2)
                                | get_field1(insn, 2, 5, 5)) as i32,
                            9,
                        );
                        if self.reg[rs1 as usize] != 0 {
                            self.pc = self.pc + imm as u64;
                            return Exception::OK;
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                self.pc += 2;
            }
            2 | 6 | 10 | 14 | 18 | 22 | 26 | 30 | 34 | 38 | 42 | 46 | 50 | 54 | 58 | 62 | 66
            | 70 | 74 | 78 | 82 | 86 | 90 | 94 | 98 | 102 | 106 | 110 | 114 | 118 | 122 | 126 => {
                let funct3 = (insn >> 13) & 7;
                let rs2 = (insn >> 2) & 0x1f;
                match funct3 {
                    0 => {
                        /* c.slli */
                        let imm = get_field1(insn, 12, 5, 5) | rs2;
                        if rd != 0 {
                            self.reg[rd] = self.reg[rd] << imm;
                        }
                    }
                    1 => {
                        /* c.fldsp */
                        let imm = get_field1(insn, 12, 5, 5)
                            | (rs2 & (3 << 3))
                            | get_field1(insn, 2, 6, 8);
                        let addr = self.reg[2] + imm as i32 as u64;
                        let mut rval = 0;
                        if self.target_read_u64(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        self.fp_reg[rd] = rval;
                        self.fs = 3;
                    }
                    2 => {
                        /* c.lwsp */
                        let imm = get_field1(insn, 12, 5, 5)
                            | (rs2 & (7 << 2))
                            | get_field1(insn, 2, 6, 7);
                        let addr = self.reg[2] + imm as i32 as u64;
                        let mut rval = 0;
                        if self.target_read_u32(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as i32 as u64;
                        }
                    }
                    3 => {
                        /* c.ldsp */
                        let imm = get_field1(insn, 12, 5, 5)
                            | (rs2 & (3 << 3))
                            | get_field1(insn, 2, 6, 8);
                        let addr = self.reg[2] + imm as i32 as u64;
                        let mut rval = 0;
                        if self.target_read_u64(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval;
                        }
                    }
                    4 => {
                        if ((insn >> 12) & 1) == 0 {
                            if rs2 == 0 {
                                /* c.jr */
                                //println!("c.jr {}\n",rd);
                                self.pc = self.reg[rd] & !1;
                                return Exception::OK;
                            } else {
                                if rd != 0 {
                                    /* c.mv */
                                    self.reg[rd] = self.reg[rs2 as usize];
                                }
                            }
                        } else {
                            if rs2 == 0 {
                                if rd == 0 {
                                    /* c.ebreak */
                                    return Exception::BREAKPOINT;
                                } else {
                                    /* c.jalr */
                                    let val = self.pc + 2;
                                    self.pc = self.reg[rd] & !1;
                                    self.reg[1] = val;
                                    return Exception::OK;
                                }
                            } else {
                                if rd != 0 {
                                    /*  */
                                    self.reg[rd] = self.reg[rd] + self.reg[rs2 as usize];
                                }
                            }
                        }
                    }
                    5 => {
                        /* c.fsdsp */
                        let imm = get_field1(insn, 10, 3, 5) | get_field1(insn, 7, 6, 8);
                        let addr = self.reg[2] + imm as i32 as u64;
                        if self.target_write_u64(self.fp_reg[rs2 as usize], addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    6 => {
                        /* c.swsp */
                        let imm = get_field1(insn, 9, 2, 5) | get_field1(insn, 7, 6, 7);
                        let addr = self.reg[2] + imm as i32 as u64;
                        if self.target_write_u32(self.reg[rs2 as usize] as u32, addr as usize) != 0
                        {
                            return Exception::StoreAccessFault;
                        }
                    }
                    7 => {
                        /* c.sdsp */
                        let imm = get_field1(insn, 10, 3, 5) | get_field1(insn, 7, 6, 8);
                        let addr = self.reg[2] + imm as i32 as u64;
                        if self.target_write_u64(self.reg[rs2 as usize], addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }

                self.pc += 2;
            }
            _ => {
                return Exception::NotCompress;
            }
        }

        Exception::OK
    }

    #[allow(arithmetic_overflow)]
    pub fn cpu_execute(&mut self, insn: u32) -> Exception {
        let opcode = insn & 0x7f;
        let rd: usize = ((insn >> 7) & 0x1f) as usize;

        let imm: i32;
        let funct3: u32;
        let mut val: u64;

        let res = self.cpu_execute_compress(insn, opcode, rd);
        if res != Exception::NotCompress {
            return res;
        }

        let rs1: usize = ((insn >> 15) & 0x1f) as usize;
        let rs2: usize = ((insn >> 20) & 0x1f) as usize;

        match opcode {
            0x37 => {
                //lui
                if rd != 0 {
                    self.reg[rd] = ((insn & 0xfffff000) as i32) as u64;
                }

                self.pc += 4;
            }
            0x17 => {
                // auipc
                if rd != 0 {
                    self.reg[rd] = self.pc + ((insn & 0xfffff000) as i32) as u64;
                }

                self.pc += 4;
            }
            0x6f => {
                //jal

                let mut imm = (((insn >> (31 - 20)) & (1 << 20))
                    | ((insn >> (21 - 1)) & 0x7fe)
                    | ((insn >> (20 - 11)) & (1 << 11))
                    | (insn & 0xff000)) as i32;
                imm = (imm << 11) >> 11;

                if rd != 0 {
                    self.reg[rd] = self.pc + 4;
                }

                self.pc += imm as i32 as u64;
            }
            0x67 => {
                //jalr
                imm = (insn as i32) >> 20;
                let val = self.pc + 4;

                self.pc = (self.reg[rs1] + imm as u64) & (!1);

                if rd != 0 {
                    self.reg[rd] = val;
                }
            }
            0x63 => {
                funct3 = (insn >> 12) & 7;

                let mut imm = (((insn >> (31 - 12)) & (1 << 12))
                    | ((insn >> (25 - 5)) & 0x7e0)
                    | ((insn >> (8 - 1)) & 0x1e)
                    | ((insn << (11 - 7)) & (1 << 11))) as i32;
                imm = (imm << 19) >> 19;

                let imm = imm as u64;
                let mut next_pc = 4;
                match funct3 {
                    0x0 => {
                        // beq
                        if self.reg[rs1] == self.reg[rs2] {
                            next_pc = imm;
                        }
                    }
                    0x1 => {
                        // bne
                        if self.reg[rs1] != self.reg[rs2] {
                            next_pc = imm;
                        }
                    }
                    0x4 => {
                        // blt

                        if (self.reg[rs1] as i64) < (self.reg[rs2] as i64) {
                            next_pc = imm;
                        }
                    }
                    0x5 => {
                        // bge
                        if (self.reg[rs1] as i64) >= (self.reg[rs2] as i64) {
                            next_pc = imm;
                        }
                    }
                    0x6 => {
                        // bltu
                        if (self.reg[rs1]) < (self.reg[rs2]) {
                            next_pc = imm;
                        }
                    }
                    0x7 => {
                        // bgeu
                        if (self.reg[rs1]) >= (self.reg[rs2]) {
                            next_pc = imm;
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                self.pc += next_pc;
            }
            0x03 => {
                funct3 = (insn >> 12) & 7;
                let offset = ((insn as i32) >> 20) as u64;
                let addr = self.reg[rs1] + offset;
                match funct3 {
                    0x0 => {
                        // lb
                        let mut rval = 0;
                        if self.target_read_u8(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as i8 as i64 as u64;
                        }
                    }
                    0x1 => {
                        // lh

                        let mut rval = 0;
                        if self.target_read_u16(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as i16 as i64 as u64;
                        }
                    }
                    0x2 => {
                        // lw
                        let mut rval = 0;
                        if self.target_read_u32(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as i32 as i64 as u64;
                        }
                    }
                    0x3 => {
                        // ld
                        let mut rval = 0;
                        if self.target_read_u64(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }

                        // println!("read addr {:X} reg {:X} val {:X} \n", addr,rd,rval);
                        if rd != 0 {
                            self.reg[rd] = rval;
                        }
                    }
                    0x4 => {
                        // lbu
                        let mut rval = 0;
                        if self.target_read_u8(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as u64;
                        }
                    }
                    0x5 => {
                        // lhu
                        let mut rval = 0;
                        if self.target_read_u16(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as u64;
                        }
                    }
                    0x6 => {
                        // lwu
                        let mut rval = 0;
                        if self.target_read_u32(&mut rval, addr as usize) != 0 {
                            return Exception::LoadAccessFault;
                        }
                        if rd != 0 {
                            self.reg[rd] = rval as u64;
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                self.pc += 4;
            }
            0x23 => {
                funct3 = (insn >> 12) & 7;

                let mut imm = rd as i32 | ((insn >> (25 - 5)) & 0xfe0) as i32;
                imm = (imm << 20) >> 20;

                let addr = self.reg[rs1] + imm as u64;
                let val = self.reg[rs2];
                match funct3 {
                    0x0 => {
                        // sb
                        if self.target_write_u8(val as u8, addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    0x1 => {
                        // sh
                        if self.target_write_u16(val as u16, addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    0x2 => {
                        // sw
                        if self.target_write_u32(val as u32, addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    0x3 => {
                        // sd

                        if self.target_write_u64(val, addr as usize) != 0 {
                            return Exception::StoreAccessFault;
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                self.pc += 4;
            }
            0x13 => {
                funct3 = (insn >> 12) & 7;
                let imm = ((insn as i32) >> 20) as u64;
                let funct7 = (insn >> 25) & 0x7f;

                match funct3 {
                    0x0 => {
                        // addi
                        val = self.reg[rs1] + imm;
                    }
                    0x1 => {
                        // slli
                        // shamt size is 5 bits for RV32I and 6 bits for RV64I.
                        let shamt = (insn >> 20) & 0x3f;
                        val = self.reg[rs1] << shamt;
                    }
                    0x2 => {
                        // slti
                        if (self.reg[rs1] as i64) < (imm as i64) {
                            val = 1;
                        } else {
                            val = 0;
                        }
                    }
                    0x3 => {
                        // sltiu
                        if self.reg[rs1] < imm {
                            val = 1;
                        } else {
                            val = 0;
                        }
                    }
                    0x4 => {
                        // xori
                        val = self.reg[rs1] ^ imm;
                    }
                    0x5 => {
                        match funct7 >> 1 {
                            0x00 => {
                                // srli
                                // shamt size is 5 bits for RV32I and 6 bits for RV64I.
                                let shamt = (insn >> 20) & 0x3f;
                                val = self.reg[rs1] >> shamt;
                            }
                            0x10 => {
                                // srai
                                // shamt size is 5 bits for RV32I and 6 bits for RV64I.
                                let shamt = (insn >> 20) & 0x3f;
                                val = ((self.reg[rs1] as i64) >> shamt) as u64;
                            }
                            _ => {
                                return Exception::IllegalInstruction;
                            }
                        }
                    }
                    0x6 => {
                        // ori
                        val = self.reg[rs1] | imm;
                    }
                    0x7 => {
                        // andi

                        val = self.reg[rs1] & imm;
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                if rd != 0 {
                    self.reg[rd] = val;
                }
                self.pc += 4;
            }
            0x1b => {
                // RV64I
                // imm[11:0] = inst[31:20]
                funct3 = (insn >> 12) & 7;

                let imm = (insn as i32) >> 20;
                val = self.reg[rs1];
                match funct3 {
                    0x0 => {
                        // addiw
                        val = (val + imm as u64) as i32 as i64 as u64;
                    }
                    0x1 => {
                        // slliw
                        // "SLLIW, SRLIW, and SRAIW encodings with imm[5] ̸= 0 are reserved."
                        val = (val << (imm & 31)) as i32 as u64;
                    }
                    0x5 => {
                        if (imm & 0x400) == 0 {
                            //srliw
                            val = (val as u32 >> (imm & 31) as u32) as i32 as u64;
                        } else {
                            //sraiw
                            val = (val as i32 >> (imm & 31)) as u64;
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                if rd != 0 {
                    self.reg[rd] = val;
                }
                self.pc += 4;
            }
            0x33 => {
                let imm = insn >> 25;
                let mut val = self.reg[rs1];
                let val2 = self.reg[rs2];
                if imm == 1 {
                    funct3 = (insn >> 12) & 7;
                    match funct3 {
                        0 => {
                            /* mul */
                            val = ((val as i64) * (val2 as i64)) as u64;
                        }
                        1 => {
                            /* mulh */
                            val = mulh64(val as i64, val2 as i64);
                        }
                        2 => {
                            /* mulhsu */
                            val = mulhsu64(val as i64, val2);
                        }
                        3 => {
                            /* mulhu */
                            val = mulhu64(val, val2);
                        }
                        4 => {
                            /* div */
                            val = div64(val as i64, val2 as i64) as u64;
                        }
                        5 => {
                            /* divu */
                            val = divu64(val, val2);
                        }
                        6 => {
                            /* rem */
                            val = rem64(val as i64, val2 as i64) as u64;
                        }
                        7 => {
                            /* remu */
                            val = remu64(val, val2);
                        }
                        _ => {
                            return Exception::IllegalInstruction;
                        }
                    }
                } else {
                    funct3 = ((insn >> 12) & 7) | ((insn >> (30 - 3)) & (1 << 3));
                    match funct3 {
                        0 => {
                            /* add */
                            val = val + val2;
                        }
                        8 => {
                            /* sub */
                            val = val - val2;
                        }
                        1 => {
                            /* sll */
                            val = val << (val2 & (64 - 1));
                        }
                        2 => {
                            /* slt */
                            let res = (val as i64) < (val2 as i64);
                            if res {
                                val = 1;
                            } else {
                                val = 0;
                            }
                        }
                        3 => {
                            /* sltu */
                            let res = val < val2;
                            if res {
                                val = 1;
                            } else {
                                val = 0;
                            }
                        }
                        4 => {
                            /* xor */
                            val = val ^ val2;
                        }
                        5 => {
                            /* srl */
                            val = val >> (val2 & (64 - 1));
                        }
                        13 => {
                            /* sra */
                            val = ((val as i64) >> (val2 & (64 - 1))) as u64;
                        }
                        6 => {
                            /* or */
                            val = val | val2;
                        }
                        7 => {
                            /* and */
                            val = val & val2;
                        }
                        _ => {
                            return Exception::IllegalInstruction;
                        }
                    }
                }

                if rd != 0 {
                    self.reg[rd] = val;
                }
                self.pc += 4;
            }
            0x3b => {
                let imm = insn >> 25;
                let mut val = self.reg[rs1];
                let val2 = self.reg[rs2];
                if imm == 1 {
                    funct3 = (insn >> 12) & 7;
                    match funct3 {
                        0 => {
                            /* mulw */
                            val = ((val as i32) * (val2 as i32)) as u64;
                        }
                        4 => {
                            /* divw */
                            val = div32(val as i32, val2 as i32) as u64;
                        }
                        5 => {
                            /* divuw */
                            val = divu32(val as u32, val2 as u32) as i32 as u64;
                        }
                        6 => {
                            /* remw */
                            val = rem32(val as i32, val2 as i32) as u64;
                        }
                        7 => {
                            /* remuw */
                            val = remu32(val as u32, val2 as u32) as i32 as u64;
                        }
                        _ => {
                            return Exception::IllegalInstruction;
                        }
                    }
                } else {
                    funct3 = ((insn >> 12) & 7) | ((insn >> (30 - 3)) & (1 << 3));
                    match funct3 {
                        0 => {
                            /* addw */
                            val = (val + val2) as i32 as u64;
                        }
                        8 => {
                            /* subw */
                            val = (val - val2) as i32 as u64;
                        }
                        1 => {
                            /* sllw */
                            val = ((val as u32) << (val2 & (32 - 1))) as i32 as u64;
                        }

                        5 => {
                            /* srlw */
                            val = ((val as u32) >> (val2 & (32 - 1))) as i32 as u64;
                        }
                        13 => {
                            /* sraw */
                            val = ((val as i32) >> (val2 & (32 - 1))) as u64;
                        }
                        _ => {
                            return Exception::IllegalInstruction;
                        }
                    }
                }

                if rd != 0 {
                    self.reg[rd] = val;
                }
                self.pc += 4;
            }
            0x0f => {
                //fence fence.i
                self.pc += 4;
            }
            0x2f => {
                let funct3 = (insn >> 12) & 7;
                let val;
                match funct3 {
                    3 => {
                        let mut rval = 0;
                        let addr = self.reg[rs1];
                        let funct3 = insn >> 27;

                        match funct3 {
                            0 | 1 | 4 | 0xc | 0x8 | 0x10 | 0x14 | 0x18 | 0x1c => {
                                if self.target_read_u64(&mut rval, addr as usize) != 0 {
                                    return Exception::LoadAccessFault;
                                }
                                val = rval;
                                let mut val2 = self.reg[rs2];
                                match funct3 {
                                    1 => {} /* amoswap.d */
                                    0 => {
                                        /* amoadd.d */
                                        val2 = val + val2;
                                    }
                                    4 => {
                                        /* amoxor.d */
                                        val2 = val ^ val2;
                                    }
                                    0xc => {
                                        /* amoand.d */
                                        val2 = val & val2;
                                    }
                                    0x8 => {
                                        /* amoor.d */
                                        val2 = val | val2;
                                    }
                                    0x10 => {
                                        /* amomin.d */
                                        if (val as i64) < (val2 as i64) {
                                            val2 = val;
                                        }
                                    }
                                    0x14 => {
                                        /* amomax.d */
                                        if (val as i64) > (val2 as i64) {
                                            val2 = val;
                                        }
                                    }
                                    0x18 => {
                                        /* amominu.d */
                                        if val < val2 {
                                            val2 = val;
                                        }
                                    }
                                    0x1c => {
                                        /* amomaxu.d */
                                        if val > val2 {
                                            val2 = val;
                                        }
                                    }
                                    _ => {}
                                }
                                if self.target_write_u64(val2, addr as usize) != 0 {
                                    return Exception::StoreAccessFault;
                                }
                            }
                            2 => {
                                //lr.d
                                if self.target_read_u64(&mut rval, addr as usize) != 0 {
                                    return Exception::LoadAccessFault;
                                }
                                val = rval;
                                self.reservation_set.push(addr);
                            }
                            3 => {
                                //sc.d
                                if self.reservation_set.contains(&addr) {
                                    self.reservation_set.retain(|&x| x != addr);
                                    if self.target_write_u64(self.reg[rs2], addr as usize) != 0 {
                                        return Exception::StoreAccessFault;
                                    }
                                    val = 0;
                                } else {
                                    self.reservation_set.retain(|&x| x != addr);
                                    val = 1;
                                }
                            }
                            _ => {
                                return Exception::IllegalInstruction;
                            }
                        }
                    }
                    2 => {
                        let mut rval = 0;
                        let addr = self.reg[rs1];
                        let funct3 = insn >> 27;

                        match funct3 {
                            0 | 1 | 4 | 0xc | 0x8 | 0x10 | 0x14 | 0x18 | 0x1c => {
                                if self.target_read_u32(&mut rval, addr as usize) != 0 {
                                    return Exception::LoadAccessFault;
                                }
                                val = rval as i32 as u64;
                                let mut val2 = self.reg[rs2];
                                match funct3 {
                                    1 => {} /* amoswap.w */
                                    0 => {
                                        /* amoadd.w */
                                        val2 = (val + val2) as i32 as u64;
                                    }
                                    4 => {
                                        /* amoxor.w */
                                        val2 = (val ^ val2) as i32 as u64;
                                    }
                                    0xc => {
                                        /* amoand.w */
                                        val2 = (val & val2) as i32 as u64;
                                    }
                                    0x8 => {
                                        /* amoor.w */
                                        val2 = (val | val2) as i32 as u64;
                                    }
                                    0x10 => {
                                        /* amomin.w */
                                        if (val as i32) < (val2 as i32) {
                                            val2 = val as i32 as u64;
                                        }
                                    }
                                    0x14 => {
                                        /* amomax.w */
                                        if (val as i32) > (val2 as i32) {
                                            val2 = val as i32 as u64;
                                        }
                                    }
                                    0x18 => {
                                        /* amominu.w */
                                        if (val as u32) < (val2 as u32) {
                                            val2 = val as i32 as u64;
                                        }
                                    }
                                    0x1c => {
                                        /* amomaxu.w */
                                        if (val as u32) > (val2 as u32) {
                                            val2 = val as i32 as u64;
                                        }
                                    }
                                    _ => {}
                                }
                                if self.target_write_u32(val2 as u32, addr as usize) != 0 {
                                    return Exception::StoreAccessFault;
                                }
                            }
                            2 => {
                                //lr.w
                                if self.target_read_u32(&mut rval, addr as usize) != 0 {
                                    return Exception::LoadAccessFault;
                                }
                                val = rval as i32 as u64;
                                self.reservation_set.push(addr);
                            }
                            3 => {
                                //sc.w
                                if self.reservation_set.contains(&addr) {
                                    self.reservation_set.retain(|&x| x != addr);
                                    if self.target_write_u32(self.reg[rs2] as u32, addr as usize)
                                        != 0
                                    {
                                        return Exception::StoreAccessFault;
                                    }

                                    val = 0;
                                } else {
                                    self.reservation_set.retain(|&x| x != addr);
                                    val = 1;
                                }
                            }
                            _ => {
                                return Exception::IllegalInstruction;
                            }
                        }
                    }
                    _ => {
                        return Exception::IllegalInstruction;
                    }
                }
                if rd != 0 {
                    self.reg[rd] = val;
                }
                self.pc += 4;
            }
            0x07 => {
                //fp load
                let funct3 = (insn >> 12) & 7;
                let imm = (insn >> 20) as i32;
                let addr = self.reg[rs1] + imm as u64;
                if funct3 == 2 {
                    let mut rval = 0;
                    if self.target_read_u32(&mut rval, addr as usize) != 0 {
                        return Exception::LoadAccessFault;
                    }
                    self.fp_reg[rd] = rval as u64 | ((u64::MAX) << 32);
                } else if funct3 == 3 {
                    let mut rval = 0;
                    if self.target_read_u64(&mut rval, addr as usize) != 0 {
                        return Exception::LoadAccessFault;
                    }
                    self.fp_reg[rd] = rval;
                } else {
                    return Exception::IllegalInstruction;
                }

                self.fs = 3;
                self.pc += 4;
            }
            0x27 => {
                //fp store
                let funct3 = (insn >> 12) & 7;
                let mut imm = rd as i32 | ((insn >> (25 - 5)) & 0xfe0) as i32;
                imm = (imm << 20) >> 20;
                let addr = self.reg[rs1] + imm as u64;
                if funct3 == 2 {
                    if self.target_write_u32(self.fp_reg[rs2] as u32, addr as usize) != 0 {
                        return Exception::StoreAccessFault;
                    }
                } else if funct3 == 3 {
                    if self.target_write_u64(self.fp_reg[rs2], addr as usize) != 0 {
                        return Exception::StoreAccessFault;
                    }
                } else {
                    return Exception::IllegalInstruction;
                }

                self.pc += 4;
            }
            0x73 => {
                let addr = insn >> 20;
                let mut funct3 = (insn >> 12) & 7;
                //let mut val = self.reg[rs1];
                if (funct3 & 4) == 0 {
                   // val = rs1 as u64;
                }
                funct3 = funct3 & 3;

                match funct3 {
                    0 => {
                        match addr {
                            0 => {
                                //ecall
                                return Exception::Ecall;
                            }

                            1 => {
                                //ebreak
                                return Exception::BREAKPOINT;
                            }
                            0x102 => { //sret
                            }
                            0x302 => { //mret
                            }
                            0x105 => { //wfi
                            }
                            _ => {
                                if (addr >> 5) == 0x09 { /* sfence.vma */
                                } else {
                                    return Exception::IllegalInstruction;
                                }
                            }
                        }
                    }
                    1 => { //csrrw
                    }
                    2 => { //csrrs
                    }
                    3 => { //csrrc
                    }
                    5 => { //csrrwi
                    }
                    6 => { //csrrsi
                    }
                    7 => { //csrrci
                    }
                    _ => {}
                }
                self.pc += 4;
            }
            _ => {
                return Exception::IllegalInstruction;
            } // TODO ^ Try commenting out this catch-all arm
        }
        Exception::OK
    }
}
