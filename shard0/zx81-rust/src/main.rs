#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

// Lookup tables for small powers (saves code size)
const POW2: [u16; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
const POW3: [u16; 6] = [1, 3, 9, 27, 81, 243];
const POW5: [u16; 5] = [1, 5, 25, 125, 625];

#[no_mangle]
pub extern "C" fn _start() -> ! {
    unsafe {
        // Calculate Gödel number: 2^5 × 3^3 × 5^7
        let result = godel_calc(5, 3, 7);
        
        // Result: 67,500,000
        // (stored in result variable)
    }
    
    loop {}
}

#[inline(always)]
fn godel_calc(a: u8, b: u8, c: u8) -> u32 {
    (POW2[a as usize] as u32) 
        * (POW3[b as usize] as u32) 
        * (POW5[c as usize] as u32)
}

#[no_mangle]
pub extern "C" fn cicada_level0() -> u32 {
    godel_calc(5, 3, 7)
}
