use crate::cpu;

/* 
#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
struct Iovec {
    base: usize,
    len: usize,
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
struct Newutsname {
    sysname: [u8; 65],
    nodename: [u8; 65],
    release: [u8; 65],
    version: [u8; 65],
    macjhine: [u8; 65],
    domian: [u8; 65],
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
struct TimeSpec {
    tv_sec: u64,
    tv_nsec: u64,
}
*/


use std::str;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn run_sys_call(machine: &mut cpu::Cpu) -> i32 {
    let call_number = machine.reg[17];
    let mut return_val = 0;

    // println!("ecall number {} pc {:X}\n", call_number, self.pc);

    match call_number {
        29 => {
            //ioctl
            return_val = 0;
        }
        64 => {
            //sys_write
            let fd = machine.reg[10];
            let start = machine.reg[11] as usize;
            let count = machine.reg[12] as usize;

            if fd == 1 {
                let sparkle_heart = str::from_utf8(&machine.code[start..start + count]).unwrap();
                println! {"{}",sparkle_heart};
            }
            return_val = count;
        }
        66 => {
            //sys_writev
            let fd = machine.reg[10];
            let mut start = machine.reg[11] as usize;
            let count = machine.reg[12] as usize;
            let mut ret = 0;

            for _i in 0..count {
                let base = usize::from_le_bytes(machine.code[start..start + 8].try_into().unwrap());
                let len =
                    usize::from_le_bytes(machine.code[start + 8..start + 16].try_into().unwrap());
                start += 16;
                if fd == 1 || fd == 2 {
                    let sparkle_heart = str::from_utf8(&machine.code[base..base + len]).unwrap();
                    println! {"{}",sparkle_heart};
                    ret += len;
                }
            }
            return_val = ret;
        }
        78 => {
            //sys_readlinkat
            return_val = usize::MAX;
        }
        79 => {
            //__NR3264_fstatat
            return_val = usize::MAX;
        }
        96 => {
            //sys_set_tid_address
            return_val = 0;
        }
        93 => {
            //sys_exit

            // println!("exit result {}\n", machine.reg[10]);
            return_val = machine.reg[10] as usize;
            machine.pc = 0x100000 - 4;
        }
        94 => {
            //sys_exit
            machine.pc = 0x100000 - 4;
        }
        99 => {
            //
            return_val = 0;
        }
        113 => {
            //sys_clock_gettime
            let start = machine.reg[11] as usize;
            let nano = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64;
            let sec = nano / 1000;
            let nn = (nano - sec * 1000) * 1000 * 1000;

            //println! {"sec {:?} nano {:?}\n",sec,nano};
            machine.code[start..start + 8].copy_from_slice(sec.to_le_bytes().as_slice());
            machine.code[start + 8..start + 16].copy_from_slice(nn.to_le_bytes().as_slice());

            return_val = 0;
        }
        160 => {
            //uname
            let addr = machine.reg[10] as usize;

            machine.code[addr..addr + 5].copy_from_slice("Linux".as_bytes());
            machine.code[addr + 65..addr + 65 + 7].copy_from_slice("unknown".as_bytes());
            machine.code[addr + 130..addr + 130 + "5.15.133.1".len()]
                .copy_from_slice("5.15.133.1".as_bytes());

            return_val = 0;
        }
        174 => {
            //getuid
            return_val = 1;
        }
        175 => {
            //geteuid
            return_val = 1;
        }

        176 => {
            //getgid
            return_val = 1;
        }
        177 => {
            //__getegid
            return_val = 1;
        }
        214 => {
            //sys_brk
            let addr = machine.reg[10] as usize;

            if addr <= 0x1100000 {
                return_val = 0x1100000;
            } else if addr <= 0x1f00000 {
                return_val = addr;
            } else {
                return_val = 0x1f00000;
            }
        }
        226 => {
            //sys_mprotect
            return_val = 0;
        }
        261 => {
            //sys_prlimit64
            return_val = 0;
        }
        278 => {
            //sys_getrandom
            return_val = usize::MAX;
        }
        _ => {
            println!("ecall number {} pc {:X}\n", call_number, machine.pc);
            return 1;
        }
    }
    machine.reg[10] = return_val as u64;
    machine.pc += 4;
    0
}
