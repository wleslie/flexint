//! Arbitrary-precision numeric types, optimized for small values.

use std::{
    cmp::Ordering,
    fmt::{self, Display, Formatter},
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign},
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
    ($Op:ident::$op:ident, $Flex:ty $(as $lhs_ref:tt)?, $Small:ty, $Big:ty, $checked_op:ident $(,)?) => {
        impl $Op<&$Small> for ref_borrow!($($lhs_ref)? $Flex) {
            type Output = $Flex;
            fn $op(self, rhs: &$Small) -> Self::Output {
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
/// Implements `$Flex ⋄= [&]$Small` by delegating to `$checked_op` and/or `$Big ⋄= $Small`.
macro_rules! assign_flex_small {
    (
        $Op:ident::$op:ident, $Flex:ty, $Small:ty $(as $rhs_ref:tt)?,
        $Big:ty, $checked_op:ident, $Binop:ident::$binop:ident $(,)?
    ) => {
        impl $Op<ref_borrow!($($rhs_ref)? $Small)> for $Flex {
            fn $op(&mut self, rhs: ref_borrow!($($rhs_ref)? $Small)) {
                match &mut self.0 {
                    Inner::Small(a) => {
                        if let Some(n) = a.$checked_op(ref_deref!($($rhs_ref)? rhs)) {
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
    ($Op:ident::$op:ident, $Lhs:ty, $Flex:ty $(as $rhs_ref:tt)? $(,)?) => {
        impl $Op<ref_borrow!($($rhs_ref)? $Flex)> for $Lhs {
            type Output = $Flex;
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
        $Op:ident::$op:ident, $OpAssign:ident::$op_assign:ident, $checked_op:ident,
        $Flex:ty, $Small:ty, $Big:ty $(,)?
    ) => {
        // &$Flex ⋄ &T
        binop_flex_small!($Op::$op, $Flex as ref, $Small, $Big, $checked_op);
        binop_flex_t!($Op::$op, $Flex as ref, &$Big);
        binop_t_flex!($Op::$op, &$Flex, $Flex as ref);

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
        binop_t_flex!($Op::$op, $Flex, $Flex as ref);

        // &$Flex ⋄ T
        trait_tactics::binop_via_binop_ref_rhs!(impl $Op<$Small> for &$Flex { fn $op -> $Flex });
        binop_flex_t!($Op::$op, $Flex as ref, $Big);
        binop_t_flex!($Op::$op, &$Flex, $Flex);

        // $Flex ⋄ T
        trait_tactics::binop_via_assign!(impl $Op<$Small> for $Flex { fn $op => $OpAssign::$op_assign });
        binop_flex_t!($Op::$op, $Flex, $Big);
        binop_t_flex!($Op::$op, $Flex, $Flex);
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

        binop_family_with_assign!(Add::add, AddAssign::add_assign, checked_add, $Flex, $Small, $Big);
        binop_family_with_assign!(Sub::sub, SubAssign::sub_assign, checked_sub, $Flex, $Small, $Big);
        binop_family_with_assign!(Mul::mul, MulAssign::mul_assign, checked_mul, $Flex, $Small, $Big);
        // Possible optimization: panic early when the divisor is zero, instead of letting
        // checked_div/checked_rem fail and falling back to bignum operations that ultimately panic
        // anyway.
        binop_family_with_assign!(Div::div, DivAssign::div_assign, checked_div, $Flex, $Small, $Big);
        binop_family_with_assign!(Rem::rem, RemAssign::rem_assign, checked_rem, $Flex, $Small, $Big);
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
