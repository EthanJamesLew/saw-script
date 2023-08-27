pub fn f(_x: u32) -> u32 {
    unimplemented!("f not overridden");
}

pub fn g(x: u32) -> u32 {
    f(x).wrapping_add(1)
}
