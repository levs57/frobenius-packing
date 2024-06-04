use std::hash::{Hash, Hasher};
use std::fmt::{Display, Formatter};
use std::fmt::Debug;
use std::ops::BitXorAssign;
use crate::field::{Field, PrimeField, BaseField, ExtensionField, FieldExtension};

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
    pub fn mul_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, multiplication by 2^k is just a left rotation by k bits.
        let exp = (exp % 31) as u8;
        let left = (self.0 << exp) & ((1 << 31) - 1);
        let right = self.0 >> (31 - exp);
        let rotated = left | right;
        Self::new(rotated)
    }

    #[inline]
    pub fn div_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, division by 2^k is just a right rotation by k bits.
        let exp = (exp % 31) as u8;
        let left = self.0 >> exp;
        let right = (self.0 << (31 - exp)) & ((1 << 31) - 1);
        let rotated = left | right;
        Self::new(rotated)
    }
}
impl Default for Mersenne31Field {
    fn default() -> Self {
        Self(0u32)
    }
}

impl PartialEq for Mersenne31Field {
    fn eq(&self, other: &Self) -> bool {
        self.to_reduced_u32() == other.to_reduced_u32()
    }
}
impl Eq for Mersenne31Field {}

impl Hash for Mersenne31Field {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.to_reduced_u32())
    }
}

impl Ord for Mersenne31Field {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_reduced_u32().cmp(&other.to_reduced_u32())
    }
}

impl PartialOrd for Mersenne31Field {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Mersenne31Field {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Debug for Mersenne31Field {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Field for Mersenne31Field {
    const ZERO: Self = Self(0);
    const ONE: Self = Self(1);

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.to_reduced_u32() == 0
    }

    fn inverse(&self) -> Option<Self>{
        //Since the nonzero elements of GF(pn) form a finite group with respect to multiplication,
        // a^p^n−1 = 1 (for a ≠ 0), thus the inverse of a is a^p^n−2.
        if self.is_zero() {
            return None;
        }
        Some(self.pow(Mersenne31Field::ORDER - 2))
    }
    
    fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
        let mut sum = self.0.wrapping_add(other.0);
        let msb = sum & (1 << 31);
        sum.bitxor_assign(msb);
        sum += u32::from(msb != 0);
        if sum >= Self::ORDER {
            sum -= Self::ORDER;
        }
        self.0 = sum;

        self
    }
    
    fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
        let mut sum = self.0.wrapping_sub(other.0);
        let msb = sum & (1 << 31);
        sum.bitxor_assign(msb);
        sum -= u32::from(msb != 0);
        self.0 = sum;

        self

    }
    
    fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self{
        let product = u64::from(self.0) * u64::from(other.0);
        let product_low = (product as u32) & ((1 << 31) - 1);
        let product_high = (product >> 31) as u32;
        *self = Self(product_low);
        self.add_assign(&Self(product_high));
        self
    }
    
    fn square(&'_ mut self) -> &'_ mut Self{
        self.mul_assign(&self.clone())
    }
    
    #[inline(always)]
    fn negate(&'_ mut self) -> &'_ mut Self{
        if self.is_zero() == false {
            *self = Self(Self::ORDER - self.to_reduced_u32());
        }
    
        self
    }
    
    fn double(&'_ mut self) -> &'_ mut Self{
        let t = *self;
        self.add_assign(&t);

        self
    }

    // TODO: could be optimized a little further?
    fn mul_by_two(&'_ mut self) -> &'_ mut Self { 
        *self = self.mul_2exp_u64(1);
        self
    }

    fn div_by_two(&'_ mut self) -> &'_ mut Self { 
        *self = self.div_2exp_u64(1);
        self
    }
}

impl PrimeField for Mersenne31Field {
    const TWO: Self = Self(2);
    const MINUS_ONE: Self = Self(Self::ORDER - 1);
    const NUM_BYTES_IN_REPR: usize = 4;
    const CHAR_BITS: usize = 31;
    const CHARACTERISTICS: u64 = Self::ORDER as u64;

    #[inline(always)]
    fn as_u64(self) -> u64 {
        self.0 as u64
    }

    #[inline(always)]
    fn from_u64_unchecked(value: u64) -> Self{
        Self::new(
            value.try_into()
                .expect("Too large"),
        )
    }
    #[inline(always)]
    fn from_u64(value: u64) -> Option<Self> {
        if value as u32 >= Self::ORDER {
            None
        } else {
            Some(Self(value as u32))
        }
    }

    #[inline(always)]
    fn from_u64_with_reduction(value: u64) -> Self {
        let val_as_u32 = value as u32;
        Self(val_as_u32 % Self::ORDER)
    }

    #[inline(always)]
    fn as_u64_reduced(&self) -> u64 {
        self.to_reduced_u32() as u64
    }

    fn as_boolean(&self) -> bool{
        let as_uint = self.to_reduced_u32();
        assert!(as_uint == 0 || as_uint == 1);
        as_uint != 0
    }

    fn from_boolean(flag: bool) -> Self {
        if flag { Self::ONE } else { Self::ZERO }
    }

    fn to_le_bytes(self) -> [u8; Self::NUM_BYTES_IN_REPR] {
        self.0.to_le_bytes()
    } 

    fn increment_unchecked(&'_ mut self) {
        self.0 += 1;
    }
}

impl BaseField for Mersenne31Field {
    const QUADRATIC_NON_RESIDUE: Mersenne31Field = Mersenne31Field::MINUS_ONE;
}
pub type Mersenne31Complex = ExtensionField<Mersenne31Field, 2>;

impl Mersenne31Complex {
    pub const fn new(real: Mersenne31Field, imag: Mersenne31Field) -> Self {
        Self { coeffs: [real, imag] }
    }

    pub fn real_part(&self) -> Mersenne31Field {
        self.coeffs[0]
    }

    pub fn imag_part(&self) -> Mersenne31Field {
        self.coeffs[1]
    }

    pub fn conjugate(&'_ mut self) -> &'_ mut Self {
        self.coeffs[1].negate();
        self
    }

    pub fn div_2exp_u64(&self, exp: u64) -> Self {
        Self::new(
            self.real_part().div_2exp_u64(exp),
            self.imag_part().div_2exp_u64(exp),
        )
    }
}

impl BaseField for Mersenne31Complex {
    // 2 + i is non-residue
    const QUADRATIC_NON_RESIDUE: Mersenne31Complex = Mersenne31Complex { 
        coeffs: [Mersenne31Field::TWO, Mersenne31Field::ONE]
    };
}
pub type Mersenne31Quartic = ExtensionField<Mersenne31Complex, 2>;


// TODO: for now it is a dirty hack and should definitely be derived automatically
impl FieldExtension<Mersenne31Field> for Mersenne31Quartic {
    const DEGREE: usize = 4;

    fn mul_assign_by_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.coeffs.iter_mut().for_each(|coef| { coef.mul_assign_by_base(elem); } );
        self
    }

    fn into_coeffs_in_base(self) -> [Mersenne31Field; 4] {
        let Mersenne31Quartic { coeffs } = self;
        let [c0, c1] = coeffs[0].into_coeffs_in_base();
        let [c2, c3] = coeffs[1].into_coeffs_in_base();
        [c0, c1, c2, c3]
    }

    fn from_coeffs_in_base(coefs: &[Mersenne31Field]) -> Self {
        let c0 = Mersenne31Complex::from_coeffs_in_base(&coefs[0..2]);
        let c1 = Mersenne31Complex::from_coeffs_in_base(&coefs[2..4]);
        Self {coeffs: [c0, c1]}
    }

    fn coeffs_in_base(&self) -> &[Mersenne31Field] {
        unsafe { std::mem::transmute::<&[Mersenne31Complex], &[Mersenne31Field]>(&self.coeffs) }
    }

    fn add_assign_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.coeffs[0].add_assign_base(elem);
        self
    }

    fn sub_assign_base(&mut self, elem: &Mersenne31Field) -> &mut Self {
        self.coeffs[0].sub_assign_base(elem);
        self
    }
    
    fn from_base(elem: Mersenne31Field) -> Self {
        let c0 = Mersenne31Complex::from_base(elem);
        Self { coeffs: [c0, Mersenne31Complex::ZERO] }
    }

    fn get_coef_mut(&mut self, idx: usize) -> &mut Mersenne31Field {
        let major_idx = if idx < 2 {0} else {1};
        self.coeffs[major_idx].get_coef_mut(idx % 2)
    }
}


pub fn rand_fp_from_rng<R: rand::Rng>(rng: &mut R) -> Mersenne31Field {
    Mersenne31Field::from_u64_unchecked(rng.gen_range(0..((1 << 31) - 1)))
}

pub fn rand_fp2_from_rng<R: rand::Rng>(rng: &mut R) -> Mersenne31Complex {
    let a = Mersenne31Field::from_u64_unchecked(rng.gen_range(0..((1 << 31) - 1)));
    let b = Mersenne31Field::from_u64_unchecked(rng.gen_range(0..((1 << 31) - 1)));
    Mersenne31Complex::new(a, b)
}


impl std::fmt::Debug for Mersenne31Complex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "F2[{}, {}]", self.coeffs[0], self.coeffs[1])
    }
}

impl std::fmt::Display for Mersenne31Complex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "F2[{}, {}]", self.coeffs[0], self.coeffs[1])
    }
}

impl std::fmt::Debug for Mersenne31Quartic{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "F4[{}, {}, {}, {}]", self.coeffs[0].coeffs[0], self.coeffs[0].coeffs[1], self.coeffs[1].coeffs[0], self.coeffs[1].coeffs[1])
    }
}

impl std::fmt::Display for Mersenne31Quartic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "F4[{}, {}, {}, {}]", self.coeffs[0].coeffs[0], self.coeffs[0].coeffs[1], self.coeffs[1].coeffs[0], self.coeffs[1].coeffs[1])
    }
}