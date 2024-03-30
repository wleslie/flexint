//! Arbitrary-precision numeric types, optimized for small values.

use std::{
    borrow::Cow,
    cmp::Ordering,
    error::Error,
    fmt::{self, Display, Formatter},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
    str::FromStr,
};

use num_bigint::{BigInt, BigUint, ParseBigIntError, Sign};
use num_integer::Integer;
use num_traits::{CheckedMul, Num, One, Pow, Signed, Unsigned, Zero};

#[cfg(feature = "serde")]
use serde_with::{DeserializeFromStr, SerializeDisplay};

// Invariant: 'Small' must be used when value fits. 'Big' shall be used *only* when value does not
// fit in 'Small'
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Inner<S, B> {
    Small(S),
    Big(B),
}

macro_rules! ref_borrow {
    (ref $($rest:tt)*) => {
        &$($rest)*
    };
    ($($rest:tt)*) => {
        $($rest)*
    };
}
macro_rules! ref_deref {
    (ref $($rest:tt)*) => {
        *$($rest)*
    };
    ($($rest:tt)*) => {
        $($rest)*
    };
}

/// Implements `[&]$Flex ⋄ &$Small` by delegating to `$checked_op` and/or `$Big ⋄ $Small`.
macro_rules! binop_flex_small {
    ($Op:ident::$op:ident, $Flex:ty $(as $lhs_ref:tt)?, $Small:ty, $Big:ty, $checked_op:expr $(,)?) => {
        impl $Op<&$Small> for ref_borrow!($($lhs_ref)? $Flex) {
            type Output = $Flex;
            fn $op(self, rhs: &$Small) -> Self::Output {
                match ref_borrow!($($lhs_ref)? self.0) {
                    Inner::Small(a) => {
                        if let Some(n) = $checked_op(ref_deref!($($lhs_ref)? a), *rhs) {
                            n.into()
                        } else {
                            $Op::$op(<$Big>::from(ref_deref!($($lhs_ref)? a)), *rhs).into()
                        }
                    }
                    Inner::Big(a) => $Op::$op(a, *rhs).into(),
                }
            }
        }
    };
}

/// Implements `$Flex ⋄= [&]$Small` by delegating to `$checked_op` and/or `$Big ⋄= $Small`.
macro_rules! assign_flex_small {
    (
        $Op:ident::$op:ident, $Flex:ty, $Small:ty $(as $rhs_ref:tt)?,
        $Big:ty, $checked_op:expr, $Binop:ident::$binop:ident $(,)?
    ) => {
        impl $Op<ref_borrow!($($rhs_ref)? $Small)> for $Flex {
            fn $op(&mut self, rhs: ref_borrow!($($rhs_ref)? $Small)) {
                match &mut self.0 {
                    Inner::Small(a) => {
                        if let Some(n) = $checked_op(*a, ref_deref!($($rhs_ref)? rhs)) {
                            *a = n;
                        } else {
                            *self = $Binop::$binop(<$Big>::from(*a), ref_deref!($($rhs_ref)? rhs)).into();
                        }
                    }
                    Inner::Big(a) => {
                        $Op::$op(a, ref_deref!($($rhs_ref)? rhs));
                        if let Ok(n) = <$Small>::try_from(&*a) {
                            *self = n.into();
                        }
                    }
                }
            }
        }
    };
}

/// Implements `[&]$Flex ⋄ T` by delegating to either `[&]$Small ⋄ T` or `[&]$Big ⋄ T`.
macro_rules! binop_flex_t {
    ($Op:ident::$op:ident, $Flex:ty $(as $lhs_ref:tt)?, $Rhs:ty $(,)?) => {
        impl $Op<$Rhs> for ref_borrow!($($lhs_ref)? $Flex) {
            type Output = $Flex;
            fn $op(self, rhs: $Rhs) -> Self::Output {
                match ref_borrow!($($lhs_ref)? self.0) {
                    Inner::Small(a) => $Op::$op(a, rhs),
                    Inner::Big(a) => $Op::$op(a, rhs),
                }.into()
            }
        }
    };
}

/// Implements `[&]$Flex ⋄ T` by delegating to `[&]$Big ⋄ T`.
macro_rules! binop_flex_t_via_big {
    ($Op:ident::$op:ident, $Flex:ty $(as $lhs_ref:tt)?, $Rhs:ty, $Big:ty $(,)?) => {
        impl $Op<$Rhs> for ref_borrow!($($lhs_ref)? $Flex) {
            type Output = $Flex;
            fn $op(self, rhs: $Rhs) -> Self::Output {
                match ref_borrow!($($lhs_ref)? self.0) {
                    Inner::Small(a) => $Op::$op(<$Big>::from(ref_deref!($($lhs_ref)? a)), rhs),
                    Inner::Big(a) => $Op::$op(a, rhs),
                }.into()
            }
        }
    };
}

/// Implements `$Flex ⋄= T` by delegating to either `$Small ⋄ T` or `$Big ⋄= T`.
macro_rules! assign_flex_t {
    ($Op:ident::$op:ident, $Flex:ty, $Rhs:ty $(as $rhs_ref:tt)?, $Small:ty, $Binop:ident::$binop:ident $(,)?) => {
        impl $Op<ref_borrow!($($rhs_ref)? $Rhs)> for $Flex {
            fn $op(&mut self, rhs: ref_borrow!($($rhs_ref)? $Rhs)) {
                match &mut self.0 {
                    Inner::Small(a) => *self = $Binop::$binop(*a, rhs).into(),
                    Inner::Big(a) => {
                        $Op::$op(a, rhs);
                        if let Ok(n) = <$Small>::try_from(&*a) {
                            *self = n.into();
                        }
                    }
                }
            }
        }
    };
}

/// Implements `T ⋄ [&]$Flex` by delegating to either `T ⋄ [&]$Small` or `T ⋄ [&]$Big`.
macro_rules! binop_t_flex {
    ($Op:ident::$op:ident, $Lhs:ty, $Flex:ty $(as $rhs_ref:tt)?, $Output:ty $(,)?) => {
        impl $Op<ref_borrow!($($rhs_ref)? $Flex)> for $Lhs {
            type Output = $Output;
            fn $op(self, rhs: ref_borrow!($($rhs_ref)? $Flex)) -> Self::Output {
                match ref_borrow!($($rhs_ref)? rhs.0) {
                    Inner::Small(b) => $Op::$op(self, b),
                    Inner::Big(b) => $Op::$op(self, b),
                }
            }
        }
    };
}

/// Implements `T ⋄= [&]$Flex` by delegating to either `T ⋄= [&]$Small` or `T ⋄= [&]$Big`.
macro_rules! assign_t_flex {
    ($Op:ident::$op:ident, $Lhs:ty, $Flex:ty $(as $rhs_ref:tt)? $(,)?) => {
        impl $Op<ref_borrow!($($rhs_ref)? $Flex)> for $Lhs {
            fn $op(&mut self, rhs: ref_borrow!($($rhs_ref)? $Flex)) {
                match ref_borrow!($($rhs_ref)? rhs.0) {
                    Inner::Small(b) => $Op::$op(self, b),
                    Inner::Big(b) => $Op::$op(self, b),
                }
            }
        }
    };
}

macro_rules! binop_family_with_assign {
    (
        $Op:ident::$op:ident, $OpAssign:ident::$op_assign:ident, $checked_op:expr,
        $Flex:ty, $Small:ty, $Big:ty $(,)?
    ) => {
        // &$Flex ⋄ &T
        binop_flex_small!($Op::$op, $Flex as ref, $Small, $Big, $checked_op);
        binop_flex_t!($Op::$op, $Flex as ref, &$Big);
        binop_t_flex!($Op::$op, &$Flex, $Flex as ref, $Flex);

        // $Flex ⋄= &T
        assign_flex_small!($OpAssign::$op_assign, $Flex, $Small as ref, $Big, $checked_op, $Op::$op);
        assign_flex_t!($OpAssign::$op_assign, $Flex, $Big as ref, $Small, $Op::$op);
        assign_t_flex!($OpAssign::$op_assign, $Flex, $Flex as ref);

        // $Flex ⋄= T
        trait_tactics::assign_via_assign_ref!(impl $OpAssign<$Small> for $Flex { fn $op_assign });
        assign_flex_t!($OpAssign::$op_assign, $Flex, $Big, $Small, $Op::$op);
        assign_t_flex!($OpAssign::$op_assign, $Flex, $Flex);

        // $Flex ⋄ &T
        binop_flex_small!($Op::$op, $Flex, $Small, $Big, $checked_op);
        binop_flex_t!($Op::$op, $Flex, &$Big);
        binop_t_flex!($Op::$op, $Flex, $Flex as ref, $Flex);

        // &$Flex ⋄ T
        trait_tactics::binop_via_binop_ref_rhs!(impl $Op<$Small> for &$Flex { fn $op -> $Flex });
        binop_flex_t!($Op::$op, $Flex as ref, $Big);
        binop_t_flex!($Op::$op, &$Flex, $Flex, $Flex);

        // $Flex ⋄ T
        trait_tactics::binop_via_assign!(impl $Op<$Small> for $Flex { fn $op => $OpAssign::$op_assign });
        binop_flex_t!($Op::$op, $Flex, $Big);
        binop_t_flex!($Op::$op, $Flex, $Flex, $Flex);
    };
}

macro_rules! impl_neg {
    ($Flex:ty $(as $ref:tt)?, $Big:ty, $checked_op:expr $(,)?) => {
        impl Neg for ref_borrow!($($ref)? $Flex) {
            type Output = $Flex;
            fn neg(self) -> Self::Output {
                match ref_borrow!($($ref)? self.0) {
                    Inner::Small(a) => {
                        if let Some(n) = $checked_op(ref_deref!($($ref)? a)) {
                            n.into()
                        } else {
                            (-<$Big>::from(ref_deref!($($ref)? a))).into()
                        }
                    }
                    Inner::Big(a) => (-a).into(),
                }
            }
        }
    };
}

macro_rules! flex_type {
    (
        $Flex:ident, $Small:ty, $Big:ty,
        from = [$($From:ty)*],
        cmp_small_big = $cmp_small_big:expr $(,)?
    ) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        #[cfg_attr(feature = "serde", derive(SerializeDisplay, DeserializeFromStr))]
        pub struct $Flex(Inner<$Small, $Big>);

        impl From<$Small> for $Flex {
            fn from(n: $Small) -> Self {
                Self(Inner::Small(n))
            }
        }
        $(
            impl From<$From> for $Flex {
                fn from(n: $From) -> Self {
                    if let Ok(n) = <$Small>::try_from(n) {
                        n.into()
                    } else {
                        Self(Inner::Big(n.into()))
                    }
                }
            }
        )*
        impl From<$Big> for $Flex {
            fn from(n: $Big) -> Self {
                Self(match n.try_into() {
                    Ok(n) => Inner::Small(n),
                    Err(e) => Inner::Big(e.into_original()),
                })
            }
        }

        impl<'a> From<&'a $Flex> for Cow<'a, $Big> {
            fn from(n: &'a $Flex) -> Self {
                match &n.0 {
                    Inner::Small(n) => Cow::Owned((*n).into()),
                    Inner::Big(n) => Cow::Borrowed(n),
                }
            }
        }
        impl From<$Flex> for $Big {
            fn from(n: $Flex) -> Self {
                match n.0 {
                    Inner::Small(n) => n.into(),
                    Inner::Big(n) => n,
                }
            }
        }
        // TODO: TryFrom<$Flex> for $Small...

        // TODO: put this in trait_tactics
        impl PartialOrd for $Flex {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $Flex {
            fn cmp(&self, other: &Self) -> Ordering {
                let cmp_small_big: fn(&$Big) -> Ordering = $cmp_small_big;
                match (&self.0, &other.0) {
                    (Inner::Small(a), Inner::Small(b)) => a.cmp(b),
                    (Inner::Small(_), Inner::Big(b)) => cmp_small_big(b),
                    (Inner::Big(a), Inner::Small(_)) => cmp_small_big(a).reverse(),
                    (Inner::Big(a), Inner::Big(b)) => a.cmp(b),
                }
            }
        }

        impl Default for $Flex {
            fn default() -> Self {
                <$Small>::default().into()
            }
        }

        impl Display for $Flex {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                match &self.0 {
                    Inner::Small(n) => write!(f, "{n}"),
                    Inner::Big(n) => write!(f, "{n}"),
                }
            }
        }

        binop_family_with_assign!(Add::add, AddAssign::add_assign, <$Small>::checked_add, $Flex, $Small, $Big);
        binop_family_with_assign!(Sub::sub, SubAssign::sub_assign, <$Small>::checked_sub, $Flex, $Small, $Big);
        binop_family_with_assign!(Mul::mul, MulAssign::mul_assign, <$Small>::checked_mul, $Flex, $Small, $Big);
        // Possible optimization: panic early when the divisor is zero, instead of letting
        // checked_div/checked_rem fail and falling back to bignum operations that ultimately panic
        // anyway.
        binop_family_with_assign!(Div::div, DivAssign::div_assign, <$Small>::checked_div, $Flex, $Small, $Big);
        binop_family_with_assign!(Rem::rem, RemAssign::rem_assign, <$Small>::checked_rem, $Flex, $Small, $Big);

        // Pow is special because the RHS is always unsigned. Also, there's no PowAssign.
        // &$Flex ** &T
        binop_flex_small!(Pow::pow, $Flex as ref, u64, $Big, checked_pow);
        binop_flex_t_via_big!(Pow::pow, $Flex as ref, &BigUint, $Big);
        binop_t_flex!(Pow::pow, &$Flex, FlexUint as ref, $Flex);
        // $Flex ** &T
        binop_flex_small!(Pow::pow, $Flex, u64, $Big, checked_pow);
        binop_flex_t_via_big!(Pow::pow, $Flex, &BigUint, $Big);
        binop_t_flex!(Pow::pow, $Flex, FlexUint as ref, $Flex);
        // &$Flex ** T
        trait_tactics::binop_via_binop_ref_rhs!(impl Pow<u64> for &$Flex { fn pow -> $Flex });
        binop_flex_t_via_big!(Pow::pow, $Flex as ref, BigUint, $Big);
        binop_t_flex!(Pow::pow, &$Flex, FlexUint, $Flex);
        // $Flex ** T
        trait_tactics::binop_via_binop_ref_rhs!(impl Pow<u64> for $Flex { fn pow -> $Flex });
        binop_flex_t_via_big!(Pow::pow, $Flex, BigUint, $Big);
        binop_t_flex!(Pow::pow, $Flex, FlexUint, $Flex);

        impl Zero for $Flex {
            fn zero() -> Self {
                Self(Inner::Small(0))
            }
            fn is_zero(&self) -> bool {
                matches!(self, Self(Inner::Small(0)))
            }
        }
        impl One for $Flex {
            fn one() -> Self {
                Self(Inner::Small(1))
            }
            fn is_one(&self) -> bool {
                matches!(self, Self(Inner::Small(1)))
            }
        }

        impl Num for $Flex {
            type FromStrRadixErr = ParseError;
            fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
                Ok(if let Ok(n) = <$Small>::from_str_radix(str, radix) {
                    n.into()
                } else {
                    <$Big>::from_str_radix(str, radix).map_err(ParseError)?.into()
                })
            }
        }
        impl FromStr for $Flex {
            type Err = ParseError;
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Self::from_str_radix(s, 10)
            }
        }

        // TODO: optimize these impls
        impl Integer for $Flex {
            fn div_floor(&self, other: &Self) -> Self {
                Cow::from(self).div_floor(&*Cow::from(other)).into()
            }
            fn mod_floor(&self, other: &Self) -> Self {
                Cow::from(self).mod_floor(&*Cow::from(other)).into()
            }
            fn gcd(&self, other: &Self) -> Self {
                Cow::from(self).gcd(&*Cow::from(other)).into()
            }
            fn lcm(&self, other: &Self) -> Self {
                Cow::from(self).lcm(&*Cow::from(other)).into()
            }
            fn is_multiple_of(&self, other: &Self) -> bool {
                Cow::from(self).is_multiple_of(&*Cow::from(other)).into()
            }
            fn is_even(&self) -> bool {
                Cow::from(self).is_even()
            }
            fn is_odd(&self) -> bool {
                Cow::from(self).is_odd()
            }
            fn div_rem(&self, other: &Self) -> (Self, Self) {
                let (div, rem) = Cow::from(self).div_rem(&*Cow::from(other));
                (div.into(), rem.into())
            }
        }
    };
}

fn checked_pow<T: One + CheckedMul>(mut base: T, mut exp: u64) -> Option<T> {
    // Exponentiation by squaring; essentially the same algorithm as used by
    // `{integer}::checked_pow` and `num_traits::checked_pow`, but the exponent type is u64, instead
    // of u32 or usize (respectively).
    if exp == 0 {
        return Some(T::one());
    }
    let mut acc = T::one();
    while exp > 1 {
        if (exp & 1) != 0 {
            acc = acc.checked_mul(&base)?;
        }
        exp /= 2;
        base = base.checked_mul(&base)?;
    }
    acc.checked_mul(&base)
}

flex_type!(
    FlexUint, u64, BigUint,
    from = [u8 u16 u32 u128 usize],
    cmp_small_big = |_| Ordering::Greater,
);

flex_type!(
    FlexInt, i64, BigInt,
    from = [u8 u16 u32 u64 u128 usize i8 i16 i32 i128 isize],
    cmp_small_big = |big| Sign::NoSign.cmp(&big.sign()),
);

// For obvious reasons, these are only implemented for unsigned integers
impl Unsigned for FlexUint {} // what is the point of this trait?

// For obvious reasons, these are only implemented for signed integers
impl_neg!(FlexInt, BigInt, i64::checked_neg);
impl_neg!(FlexInt as ref, BigInt, i64::checked_neg);
impl Signed for FlexInt {
    fn abs(&self) -> Self {
        match &self.0 {
            Inner::Small(n) => {
                if let Some(n) = n.checked_abs() {
                    n.into()
                } else {
                    BigInt::from(*n).abs().into()
                }
            }
            Inner::Big(n) => n.abs().into(),
        }
    }
    fn abs_sub(&self, other: &Self) -> Self {
        if self > other {
            self - other
        } else {
            other - self
        }
    }
    fn signum(&self) -> Self {
        match &self.0 {
            Inner::Small(n) => n.signum().into(),
            Inner::Big(n) => n.signum().into(),
        }
    }
    fn is_positive(&self) -> bool {
        match &self.0 {
            Inner::Small(n) => n.is_positive(),
            Inner::Big(n) => n.is_positive(),
        }
    }
    fn is_negative(&self) -> bool {
        match &self.0 {
            Inner::Small(n) => n.is_negative(),
            Inner::Big(n) => n.is_negative(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParseError(ParseBigIntError);
impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl Error for ParseError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checked_pow() {
        assert_eq!(checked_pow(3u64, 19), Some(1162261467));
        assert_eq!(checked_pow(5u64, 12), Some(244140625));
    }
}
