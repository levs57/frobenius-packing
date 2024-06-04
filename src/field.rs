use core::intrinsics::transmute_unchecked;
use std::sync::atomic::AtomicU64;
use rand::Rng;
pub trait Rand {
    fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self;
}
pub trait Field: 
'static
+ Clone
+ Copy
+ Default
+ std::fmt::Display
+ std::fmt::Debug
+ std::hash::Hash
+ std::cmp::PartialEq
+ std::cmp::Eq
+ std::marker::Send
+ std::marker::Sync
+ std::default::Default
+ Rand
+ Sized
{
const ZERO: Self;
const ONE: Self;

fn inverse(&self) -> Option<Self>;

fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self;

fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self;

fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self;

fn square(&'_ mut self) -> &'_ mut Self;

fn negate(&'_ mut self) -> &'_ mut Self;

fn double(&'_ mut self) -> &'_ mut Self;

fn pow(&self, mut exp: u64) -> Self {
    let mut base = self.clone();
    let mut result = Self::ONE;
    while exp > 0 {
        if exp % 2 == 1 {
            result.mul_assign(&base);
        }

        exp >>= 1;
        base.square();
    }

    result
}

fn mul_by_two(&'_ mut self) -> &'_ mut Self { unimplemented!() }
fn div_by_two(&'_ mut self) -> &'_ mut Self { unimplemented!() }
}

pub trait PrimeField : Field {
const TWO: Self;
const MINUS_ONE: Self;
const NUM_BYTES_IN_REPR: usize;

const CHAR_BITS: usize;
const CHARACTERISTICS: u64;

fn as_u64(self) -> u64;
fn from_u64_unchecked(value: u64) -> Self;
fn from_u64_with_reduction(value: u64) -> Self;
fn from_u64(value: u64) -> Option<Self>;
fn as_u64_reduced(&self) -> u64;

fn as_boolean(&self) -> bool; 

fn from_boolean(flag: bool) -> Self {
    if flag { Self::ONE } else { Self::ZERO }
}

fn to_le_bytes(self) -> [u8; Self::NUM_BYTES_IN_REPR];  

fn increment_unchecked(&'_ mut self);
}

pub trait FrobeniusPacking<B : BaseField + PrimeField> : FieldExtension<B> + Field {
    const x: AtomicU64;

    /// Performs Frobenius mapping in place.
    fn frob(&mut self, k: usize) -> ();    

    fn frob_naive(&mut self, mut k: usize) -> () {
        k %= Self::DEGREE;
        for _ in 0..k {
            *self = self.pow(B::CHARACTERISTICS as u64)
        }
    }

}

// this field can be used as base field for quadratic extension
pub trait BaseField : Field {
const QUADRATIC_NON_RESIDUE: Self;

fn mul_by_non_residue(elem: &mut Self) {
   elem.mul_assign(&Self::QUADRATIC_NON_RESIDUE); 
}
}

#[repr(C)]
#[derive(Clone, Copy, Hash)]
// #[derive(Clone, Copy, Hash)]
pub struct ExtensionField<F: Field, const DEGREE: usize> {
pub coeffs: [F; DEGREE],
}

impl<F: Field, const DEGREE: usize> std::cmp::PartialEq for ExtensionField<F, DEGREE>
{
#[inline(always)]
fn eq(&self, other: &Self) -> bool {
    self.coeffs.iter().zip(other.coeffs.iter()).all(|(x, y)| x.eq(y))
}
}

impl<F: Field, const DEGREE: usize> std::cmp::Eq for ExtensionField<F, DEGREE> {}

impl<F: Field, const DEGREE: usize> std::default::Default for ExtensionField<F, DEGREE>
{
#[inline(always)]
fn default() -> Self {
    ExtensionField {
        coeffs: [F::default(); DEGREE]
    }
}
}


impl<F: BaseField> Field for ExtensionField<F, 2> 
where ExtensionField<F, 2>: std::fmt::Debug + std::fmt::Display
{
const ZERO: Self = ExtensionField { coeffs: [F::ZERO; 2] };
const ONE: Self = ExtensionField { coeffs: [F::ONE, F::ZERO] };

#[inline]
fn add_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
    self.coeffs[0].add_assign(&other.coeffs[0]);
    self.coeffs[1].add_assign(&other.coeffs[1]);

    self
}

#[inline]
fn sub_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
    self.coeffs[0].sub_assign(&other.coeffs[0]);
    self.coeffs[1].sub_assign(&other.coeffs[1]);

    self
}

#[inline]
fn mul_assign(&'_ mut self, other: &Self) -> &'_ mut Self {
    let mut v0 = self.coeffs[0];
    v0.mul_assign(&other.coeffs[0]);
    let mut v1 = self.coeffs[1];
    v1.mul_assign(&other.coeffs[1]);

    let t = self.coeffs[0];
    self.coeffs[1].add_assign(&t);

    let mut t0 = other.coeffs[0];
    t0.add_assign(&other.coeffs[1]);
    self.coeffs[1].mul_assign(&t0);
    self.coeffs[1].sub_assign(&v0);
    self.coeffs[1].sub_assign(&v1);
    self.coeffs[0] = v0;
    F::mul_by_non_residue(&mut v1);
    self.coeffs[0].add_assign(&v1);

    self
}

#[inline]
fn square(&'_ mut self) -> &'_ mut Self {
    let mut v0 = self.coeffs[0];
    v0.sub_assign(&self.coeffs[1]);
    let mut v3 = self.coeffs[0];
    let mut t0 = self.coeffs[1];
    F::mul_by_non_residue(&mut t0);
    v3.sub_assign(&t0);
    let mut v2 = self.coeffs[0];
    v2.mul_assign(&self.coeffs[1]);
    v0.mul_assign(&v3);
    v0.add_assign(&v2);

    self.coeffs[1] = v2;
    self.coeffs[1].double();
    self.coeffs[0] = v0;
    F::mul_by_non_residue(&mut v2);
    self.coeffs[0].add_assign(&v2);
    self
}

#[inline]
fn negate(&'_ mut self) -> &'_ mut Self {
    self.coeffs[0].negate();
    self.coeffs[1].negate();
    self
}

#[inline]
fn double(&mut self) -> &'_ mut Self {
    self.coeffs[0].double();
    self.coeffs[1].double();
    self
}

fn inverse(&self) -> Option<Self> {
    let mut v0 = self.coeffs[0];
    v0.square();
    let mut v1 = self.coeffs[1];
    v1.square();
    // v0 = v0 - beta * v1
    let mut v1_by_nonresidue = v1;
    F::mul_by_non_residue(&mut v1_by_nonresidue);
    v0.sub_assign(&v1_by_nonresidue);
    match v0.inverse() {
        Some(inversed) => {
            let mut c0 = self.coeffs[0];
            c0.mul_assign(&inversed);
            let mut c1 = self.coeffs[1];
            c1.mul_assign(&inversed);
            c1.negate();

            let new = Self { coeffs: [c0, c1] };
            Some(new)
        }
        None => None,
    }
}

#[inline]
fn mul_by_two(&'_ mut self) -> &'_ mut Self { 
    self.coeffs[0].mul_by_two();
    self.coeffs[1].mul_by_two();
    self
}

#[inline]
fn div_by_two(&'_ mut self) -> &'_ mut Self { 
    self.coeffs[0].div_by_two();
    self.coeffs[1].div_by_two();
    self
}
}


pub trait FieldExtension<BaseField: Field> {
const DEGREE: usize;
fn mul_assign_by_base(&mut self, elem: &BaseField) -> &mut Self;
fn into_coeffs_in_base(self) -> [BaseField; Self::DEGREE];
fn from_coeffs_in_base(coefs: &[BaseField]) -> Self;
fn coeffs_in_base(&self) -> &[BaseField];
fn add_assign_base(&mut self, elem: &BaseField) -> &mut Self;
fn sub_assign_base(&mut self, elem: &BaseField) -> &mut Self;
fn from_base(elem: BaseField) -> Self;
fn get_coef_mut(&mut self, idx: usize) -> &mut BaseField;
}

impl<F: Field> FieldExtension<F> for F {
const DEGREE: usize = 1;
#[inline(always)]
fn from_coeffs_in_base(coefs: &[F]) -> Self { coefs[0] }

#[inline(always)]
fn into_coeffs_in_base(self) -> [Self; 1] { [self] }

#[inline(always)]
fn coeffs_in_base(&self) -> &[F] {
    std::slice::from_ref(self)
}

#[inline(always)]
fn mul_assign_by_base(&mut self, elem: &F) -> &mut Self { self.mul_assign(elem) }

#[inline(always)]
fn add_assign_base(&mut self, elem: &F) -> &mut Self {
    self.add_assign(elem)
}

#[inline(always)]
fn sub_assign_base(&mut self, elem: &F) -> &mut Self {
    self.sub_assign(elem)
}

#[inline(always)]
fn from_base(elem: F) -> Self {
    elem
}

#[inline(always)]
fn get_coef_mut(&mut self, idx: usize) -> &mut F {
    assert_eq!(idx, 0);
    self
}
}


impl<F: Field, const N: usize> FieldExtension<F> for ExtensionField<F, N> 
{
const DEGREE: usize = N;
#[inline(always)]
fn mul_assign_by_base(&mut self, base: &F) -> &mut Self
{
    self.coeffs.iter_mut().for_each(|x| { x.mul_assign(base); });
    self
}

#[inline(always)]
fn add_assign_base(&mut self, elem: &F) -> &mut Self {
    self.coeffs[0].add_assign(elem);
    self
}

#[inline(always)]
fn sub_assign_base(&mut self, elem: &F) -> &mut Self {
    self.coeffs[0].sub_assign(elem);
    self
}

#[inline(always)]
fn into_coeffs_in_base(self) -> [F; Self::DEGREE] {
    unsafe {
        transmute_unchecked::<_, [F; Self::DEGREE]>(self.coeffs)
    }
}

#[inline(always)]
fn coeffs_in_base(&self) -> &[F] {
    &self.coeffs
} 

#[inline(always)]
fn from_coeffs_in_base(coeffs: &[F]) -> Self {
    Self { coeffs: coeffs.try_into().unwrap() }
}

#[inline(always)]
fn from_base(elem: F) -> Self {
    let mut coeffs =  std::array::from_fn(|idx: usize| {
        if idx == 0 { elem } else { F::ZERO }
    });
    Self { coeffs }
}

#[inline(always)]
fn get_coef_mut(&mut self, idx: usize) -> &mut F {
    &mut self.coeffs[idx]
}
}



impl<F: PrimeField> Rand for F {
fn random_element<R: Rng + ?Sized>(rng: &mut R) -> F {
    F::from_u64_unchecked(rng.gen_range(0..F::CHARACTERISTICS))
}
}

impl<F: Field + Rand, const DEGREE: usize> Rand for ExtensionField<F, DEGREE> {
fn random_element<R: Rng + ?Sized>(rng: &mut R) -> Self {
    Self {
        coeffs: std::array::from_fn(|_: usize| F::random_element(rng))
    }
}
}