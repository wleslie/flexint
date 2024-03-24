//! Arbitrary-precision numeric types, optimized for small values.

use std::{
    cmp::Ordering,
    fmt::{self, Display, Formatter},
    // ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

use num_bigint::{BigInt, BigUint, Sign};

// Invariant: 'Small' must be used when value fits. 'Big' shall be used *only* when value does not
// fit in 'Small'
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Inner<S, B> {
    Small(S),
    Big(B),
}

#[cfg(nope)]
macro_rules! binop_inner {
    () => {};
}

#[cfg(nope)]
macro_rules! binops_with_assign {
    (
        $Flex:ident, $Small:ty, $Big:ty,
        $({
            $Op:ty, $method:ident, $OpAssign:ty, $method_assign:ident,
            $checked_method:ident, $general_fn:expr $(,)?
        }),* $(,)?
    ) => {
        $(
            impl $Op for &$Flex {
                type Output = $Flex;
                fn $method(self, rhs: Self) -> Self::Output {
                    // let small_small_fn: fn($Small, $Small) -> Option<$Small> = $small_fn;
                    let small_big_fn: fn($Small, &$Big) -> $Big = $general_fn;
                    let big_small_fn: fn(&$Big, $Small) -> $Big = $general_fn;
                    let big_big_fn: fn(&$Big, &$Big) -> $Big = $general_fn;
                    match (&self.0, &rhs.0) {
                        (Inner::Small(a), Inner::Small(b)) => {
                            if let Some(n) = <$Small>::$checked_method(*a, *b) {
                                $Flex(Inner::Small(n))
                            } else {
                                big_small_fn(&(*a).into(), *b).into()
                            }
                        }
                        (Inner::Small(a), Inner::Big(b)) => small_big_fn(*a, b).into(),
                        (Inner::Big(a), Inner::Small(b)) => big_small_fn(a, *b).into(),
                        (Inner::Big(a), Inner::Big(b)) => big_big_fn(a, b).into(),
                    }
                }
            }
            trait_tactics::assign_via_binop_ref_lhs!(impl $OpAssign<&Self> for $Flex { fn $method_assign => $Op::$method });
            trait_tactics::assign_via_assign_ref!(impl $OpAssign for $Flex { fn $method_assign });
            trait_tactics::binop_via_assign!(impl $Op<&Self> for $Flex { fn $method => $OpAssign::$method_assign });
            trait_tactics::binop_via_binop_ref_rhs!(impl $Op<$Flex> for &$Flex { fn $method -> $Flex });
            trait_tactics::binop_via_assign!(impl $Op for $Flex { fn $method => $OpAssign::$method_assign });
        )*
    };
}

macro_rules! flex_type {
    (
        $Flex:ident, $Small:ty, $Big:ty,
        from = [$($From:ty)*],
        cmp_small_big = $cmp_small_big:expr $(,)?
    ) => {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

        impl From<$Flex> for $Big {
            fn from(n: $Flex) -> Self {
                match n.0 {
                    Inner::Small(n) => n.into(),
                    Inner::Big(n) => n,
                }
            }
        }

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
                Self(Inner::Small(Default::default()))
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

        // binops_with_assign!(
        //     $Flex, $Small, $Big,
        //     {Add, add, AddAssign, add_assign, checked_add, |a, b| a + b},
        //     {Sub, sub, SubAssign, sub_assign, checked_sub, |a, b| a - b},
        //     {Mul, mul, MulAssign, mul_assign, checked_mul, |a, b| a * b},
        //     {Div, div, DivAssign, div_assign, checked_div, |a, b| a / b},
        // );
    };
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
