//! Arbitrary-precision numeric types, optimized for small values.

use std::{
    cmp::Ordering,
    fmt::{self, Display, Formatter},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

use num_bigint::{BigInt, BigUint, Sign};

// Invariant: 'Small' must be used when value fits. 'Big' shall be used *only* when value does not
// fit in 'Small'
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Inner<S, B> {
    Small(S),
    Big(B),
}

macro_rules! ref_borrow {
    (ref $e:expr) => {
        &$e
    };
    ($e:expr) => {
        $e
    };
}
macro_rules! ref_deref {
    (ref $e:expr) => {
        *$e
    };
    ($e:expr) => {
        $e
    };
}

/// Implpments `[&]$Flex ⋄ &$Small` by delegating to either `$checked_op` or `$Big ⋄ $Small`.
macro_rules! binop_small {
    (
        impl $Op:ident<$Rhs:ty> for $Lhs:ty {
            fn $op:ident -> $Output:ty => $Big:ty, $checked_op:ident { $($lhs_ref:tt)? }
        }
    ) => {
        impl $Op<$Rhs> for $Lhs {
            type Output = $Output;
            fn $op(self, rhs: $Rhs) -> Self::Output {
                match ref_borrow!($($lhs_ref)? self.0) {
                    Inner::Small(a) => {
                        if let Some(n) = a.$checked_op(*rhs) {
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
macro_rules! assign_small {
    (
        impl $Op:ident<$Rhs:ty> for $Lhs:ty {
            fn $op:ident => $Small:ty, $Big:ty, $checked_op:ident, $Binop:ident::$binop:ident
        }
    ) => {
        impl $Op<$Rhs> for $Lhs {
            fn $op(&mut self, rhs: $Rhs) {
                match &mut self.0 {
                    Inner::Small(a) => {
                        if let Some(n) = a.$checked_op(*rhs) {
                            *a = n;
                        } else {
                            *self = $Binop::$binop(<$Big>::from(*a), *rhs).into();
                        }
                    }
                    Inner::Big(a) => {
                        $Op::$op(a, *rhs);
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
macro_rules! binop_lhs_flex {
    (
        impl $Op:ident<$Rhs:ty> for $Lhs:ty {
            fn $op:ident -> $Output:ty { $($lhs_ref:tt)? }
        }
    ) => {
        impl $Op<$Rhs> for $Lhs {
            type Output = $Output;
            fn $op(self, rhs: $Rhs) -> Self::Output {
                match ref_borrow!($($lhs_ref)? self.0) {
                    Inner::Small(a) => $Op::$op(a, rhs),
                    Inner::Big(a) => $Op::$op(a, rhs),
                }.into()
            }
        }
    };
}
/// Implements `$Flex ⋄= T` by delegating to either `$Small ⋄ T` or `$Big ⋄= T`.
macro_rules! assign_lhs_flex {
    (
        impl $Op:ident<$Rhs:ty> for $Lhs:ty {
            fn $op:ident => $Small:ty, $Binop:ident::$binop:ident
        }
    ) => {
        impl $Op<$Rhs> for $Lhs {
            fn $op(&mut self, rhs: $Rhs) {
                match &mut self.0 {
                    Inner::Small(a) => *self = $Binop::$binop(*a, rhs).into(),
                    Inner::Big(a) => {
                        *a += rhs;
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
macro_rules! binop_rhs_flex {
    (
        impl $Op:ident<$Rhs:ty> for $Lhs:ty {
            fn $op:ident -> $Output:ty { $($rhs_ref:tt)? }
        }
    ) => {
        impl $Op<$Rhs> for $Lhs {
            type Output = $Output;
            fn $op(self, rhs: $Rhs) -> Self::Output {
                match ref_borrow!($($rhs_ref)? rhs.0) {
                    Inner::Small(b) => $Op::$op(self, b),
                    Inner::Big(b) => $Op::$op(self, b),
                }
            }
        }
    };
}
/// Implements `T ⋄= [&]$Flex` by delegating to either `T ⋄= [&]$Small` or `T ⋄= [&]$Big`.
macro_rules! assign_rhs_flex {
    (
        impl $Op:ident<$Rhs:ty> for $Lhs:ty {
            fn $op:ident { $($rhs_ref:tt)? }
        }
    ) => {
        impl $Op<$Rhs> for $Lhs {
            fn $op(&mut self, rhs: $Rhs) {
                match ref_borrow!($($rhs_ref)? rhs.0) {
                    Inner::Small(b) => $Op::$op(self, b),
                    Inner::Big(b) => $Op::$op(self, b),
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

        // 0.
        binop_small!(impl Add<&$Small> for &$Flex { fn add -> $Flex => $Big, checked_add {ref} });
        binop_lhs_flex!(impl Add<&$Big> for &$Flex { fn add -> $Flex {ref} });
        binop_rhs_flex!(impl Add<Self> for &$Flex { fn add -> $Flex {ref} });

        // 1.
        assign_small!(impl AddAssign<&$Small> for $Flex { fn add_assign => $Small, $Big, checked_add, Add::add });
        assign_lhs_flex!(impl AddAssign<&$Big> for $Flex { fn add_assign => $Small, Add::add });
        assign_rhs_flex!(impl AddAssign<&$Flex> for $Flex { fn add_assign {ref} });

        // 2.
        trait_tactics::assign_via_assign_ref!(impl AddAssign<$Small> for $Flex { fn add_assign });
        assign_lhs_flex!(impl AddAssign<$Big> for $Flex { fn add_assign => $Small, Add::add });
        assign_rhs_flex!(impl AddAssign<Self> for $Flex { fn add_assign {} });

        // 3.
        binop_small!(impl Add<&$Small> for $Flex { fn add -> $Flex => $Big, checked_add {} });
        binop_lhs_flex!(impl Add<&$Big> for $Flex { fn add -> Self {} });
        binop_rhs_flex!(impl Add<&Self> for $Flex { fn add -> Self {ref} });

        // 4.
        trait_tactics::binop_via_binop_ref_rhs!(impl Add<$Small> for &$Flex { fn add -> $Flex });
        binop_lhs_flex!(impl Add<$Big> for &$Flex { fn add -> $Flex {ref} });
        binop_rhs_flex!(impl Add<$Flex> for &$Flex { fn add -> $Flex {ref} });

        // 5.
        trait_tactics::binop_via_assign!(impl Add<$Small> for $Flex { fn add => AddAssign::add_assign });
        binop_lhs_flex!(impl Add<$Big> for $Flex { fn add -> Self {} });
        binop_rhs_flex!(impl Add<Self> for $Flex { fn add -> Self {} });
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
