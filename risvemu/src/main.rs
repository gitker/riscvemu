use risvemu::cpu;
use risvemu::elf;
use risvemu::syscall;
use std::fs::File;
use std::io::{Read, Result};


fn read_binary_file(file_path: &str) -> Result<Vec<u8>> {
    // 打开文件
    let mut file = File::open(file_path)?;

    // 申请内存
    let mut buffer = Vec::new();

    // 读取文件内容到内存中
    file.read_to_end(&mut buffer)?;

    Ok(buffer)
}



use std::env;

fn test(path: &String) {
    let mut cpu = cpu::Cpu::new();

    let mut entry = 0;

    cpu.code.resize(0x2000000, 0);

    //let file_path = "rv64ui-p-add";
    match read_binary_file(path.as_str()) {
        Ok(content) => {
            // 在这里使用 content，它是一个 Vec<u8>，包含了文件的二进制内容

            elf::load_elf(content, &mut cpu.code, &mut entry);

            //println!("Hello, world {:X} !", content.len() );
        }
        Err(err) => {
            eprintln!("读取文件出错：{}", err);
        }
    }

    cpu.pc = entry as u64;
    cpu.reg[1] = 0x100000; //lr return address
    cpu.reg[2] = 0xf00000; //stack pointer
    cpu.code_ptr = cpu.code.as_mut_ptr() as usize;

   

    loop {
        if cpu.pc == 0x100000 {
            //  println!("break !");
            if cpu.reg[10] != 0 {
                println!("{} {}\n", path, cpu.reg[10]);
            }
            break;
        }
        let insn = cpu.cpu_fetch_ins();

        //println!("{:X} {:X} \n", cpu.pc,insn as u32);

        match cpu.cpu_execute(insn) {
            cpu::Exception::OK => {}
            cpu::Exception::IllegalInstruction => {
                println!("illegal {:X} {:X}!", cpu.pc, insn);
                break;
            }
            cpu::Exception::BREAKPOINT => {}
            cpu::Exception::NotCompress => {}
            cpu::Exception::LoadAccessFault => {
                println!("laod error !");
                break;
            }
            cpu::Exception::StoreAccessFault => {
                println!("store error !");
                break;
            }
            cpu::Exception::Ecall => {
                if syscall::run_sys_call(&mut cpu) != 0 {
                    break;
                }
            }
        }
    }
    //println!("读取到的文件内容长度：{}", cpu.code.len());
}

fn main() {
    let args: Vec<String> = env::args().collect();
    for (index, value) in args.iter().enumerate() {
        // println!("{} => {}", index,value );
        if index != 0 {
            test(value);
        }else {
            test(&String::from("rsa_test"));
        }
    }
}
