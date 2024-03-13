#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct Elfhdr {
    magic: u32,
    elf: [u8; 12],
    types: u16,
    machine: u16,
    version: u32,
    entry: u64,
    phoff: u64,
    shoff: u64,
    flags: u32,
    ehsize: u16,
    phentsize: u16,
    phnum: u16,
    shentsize: u16,
    shnum: u16,
    shstrndex: u16,
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct Proghdr {
    types: u32,
    flags: u32,
    off: u64,
    vaddr: u64,
    paddr: u64,
    filesz: u64,
    memsz: u64,
    align: u64,
}

#[repr(C, packed)]
#[derive(Debug, Copy, Clone)]
pub struct Sectionhdr {
    name: u32,
    types: u32,
    flags: u64,
    addr: u64,
    offset: u64,
    size: u64,
    link: u32,
    info: u32,
    addralign: u64,
    entsize: u64,
}

const ELF_PROG_LOAD: u32 = 1;

use std::mem;
pub fn load_elf(vv: Vec<u8>, dst: &mut Vec<u8>, entry: &mut usize) -> u32 {
    let vec_base = vv.as_ptr() as usize;
    let vec_end = vv.len() + vec_base;

    if vec_base + mem::size_of::<Elfhdr>() > vec_end {
        panic!("elf eror");
    }

    let elfhdr_ptr: Elfhdr = unsafe { std::ptr::read(vec_base as *const Elfhdr) };

    let phoff = elfhdr_ptr.phoff;
    let phnum = elfhdr_ptr.phnum as u64;
    let phentsize = elfhdr_ptr.phentsize as u64;
    let mut base_addr = usize::MAX;

    //println!("{:?}\n", elfhdr_ptr);

    for i in 0..phnum {
        let phbase = vec_base + (phoff + i * phentsize) as usize;
        let head: Proghdr = unsafe { std::ptr::read(phbase as *const Proghdr) };
        //  println!("{:?}\n", head);
        if head.types == ELF_PROG_LOAD {
            if (head.paddr as usize) < base_addr {
                base_addr = head.paddr as usize;
            }
        }
    }

    let mut image_size = 0;
    for i in 0..phnum {
        let phbase = vec_base + (phoff + i * phentsize) as usize;
        let head: Proghdr = unsafe { std::ptr::read(phbase as *const Proghdr) };
        let off = head.off as usize;
        let filesz = head.filesz as usize;
        let paddr = head.paddr as usize;
        if head.types == ELF_PROG_LOAD {
            dst[paddr..(filesz + paddr)].copy_from_slice(&vv[off..off + filesz]);

            if paddr - base_addr + head.memsz as usize > image_size {
                image_size = head.paddr as usize - base_addr + head.memsz as usize;
            }
        }
    }
    *entry = elfhdr_ptr.entry as usize;

    // println!(
    //     "elf entry 0x{:X} base_addr 0x{:X} image_size {}\n",
    //     *entry, base_addr, image_size
    // );

    image_size as u32
}
