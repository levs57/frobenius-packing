#[derive(Clone, Copy)]
pub struct Mersenne31Field(pub u32);


impl Mersenne31Field{
    pub const ORDER: u32 = (1 << 31) - 1;
    pub const fn new(value: u32) -> Self{
        debug_assert!((value >> 31) == 0);
        
        Self(value)
    }

    #[inline(always)]
    const fn to_reduced_u32(&self) -> u32 {
        let mut c = self.0;
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        c
    }

    pub const fn from_nonreduced_u32(c: u64) -> Self {
        let mut c = c as u32;
        if c >= Self::ORDER {
            c -= Self::ORDER;
        }
        Self::new(c)
    }
}