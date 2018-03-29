//! Internal macros

macro_rules! vector_additon {
    ($sum:ty, $ctr:expr, $basis:ty, $clone:expr) => {
        impl<'a, 'b> ::std::ops::Add<&'b $sum> for &'a $sum {
            type Output = $sum;
            fn add(self, that: &'b $sum) -> $sum {
                $ctr(self.0.symmetric_difference(&that.0).map($clone).collect::<::linked_hash_set::LinkedHashSet<_>>())
            }
        }

        impl<'a> ::std::ops::Add<$sum> for &'a $sum {
            type Output = $sum;
            #[inline]
            fn add(self, that: $sum) -> $sum {
                self + &that
            }
        }

        impl<'b> ::std::ops::Add<&'b $sum> for $sum {
            type Output = $sum;
            #[inline]
            fn add(self, that: &'b $sum) -> $sum {
                &self + that
            }
        }

        impl ::std::ops::Add<$sum> for $sum {
            type Output = $sum;
            #[inline]
            fn add(self, that: $sum) -> $sum {
                &self + &that
            }
        }

        impl<'a> ::std::ops::AddAssign<&'a $sum> for $sum {
            fn add_assign(&mut self, that: &'a $sum) {
                self.0 = self.0.symmetric_difference(&that.0).map($clone).collect::<::linked_hash_set::LinkedHashSet<_>>()
            }
        }

        impl ::std::ops::AddAssign<$sum> for $sum {
            fn add_assign(&mut self, that: $sum) {
                *self += &that
            }
        }

        impl ::std::ops::AddAssign<$basis> for $sum {
            fn add_assign(&mut self, that: $basis) {
                if !self.0.remove(&that) {
                    self.0.insert(that);
                }
            }
        }
    }
}

macro_rules! extra_mul {
    ($basis:ty) => {
        impl Mul<$basis> for $basis {
            type Output = <&'static $basis as Mul<&'static $basis>>::Output;
            fn mul(self, that: $basis) -> Self::Output {
                &self * &that
            }
        }

        impl<'a> Mul<&'a $basis> for $basis {
            type Output = <&'static $basis as Mul<&'a $basis>>::Output;
            fn mul(self, that: &'a $basis) -> Self::Output {
                &self * that
            }
        }

        impl<'a> Mul<$basis> for &'a $basis {
            type Output = <&'a $basis as Mul<&'static $basis>>::Output;
            fn mul(self, that: $basis) -> Self::Output {
                self * &that
            }
        }
    }
}