pub struct S1 {
    pub x1: u32,
    pub y1: u32,
}

pub fn f1(s: S1) -> S1 {
    S1 {
        x1: s.y1.wrapping_add(1),
        y1: s.x1.wrapping_add(2),
    }
}

// Polymorphism

pub struct S2<A, B> {
    pub x2: A,
    pub y2: B,
}

pub fn f2(s: S2<u32, u32>) -> S2<u32, u32> {
    S2 {
        x2: s.y2.wrapping_add(1),
        y2: s.x2.wrapping_add(2),
    }
}

// TODO RGS: Newtype
