/// NOTE: Not quite as efficient as the old NonZero, but good enough for now (and we want to avoid
/// code that isn't safe).  We could make it just as efficient if NonZero were implemented for
/// signed integer types, but alas...

pub trait Zeroable {
    fn is_zero(&self) -> bool;
}

macro_rules! impl_zeroable_for_integer_types {
    ( $( $Int: ty )+ ) => {
        $(
            impl Zeroable for $Int {
                #[inline]
                fn is_zero(&self) -> bool {
                    *self == 0
                }
            }
        )+
    }
}

impl_zeroable_for_integer_types! {
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Debug, Hash)]
pub struct NonZero<T: Zeroable>(T);

impl<T: Zeroable> NonZero<T> {
    /// Creates an instance of NonZero with the provided value.
    /// You must indeed ensure that the value is actually "non-zero".
    #[inline]
    pub const fn new_unchecked(inner: T) -> Self {
        // NOTE: Since this version isn't relied on for compiler optimizations, we can keep this
        // method safe.
        NonZero(inner)
    }

    /// Creates an instance of NonZero with the provided value.
    #[inline]
    pub fn new(inner: T) -> Option<Self> {
        if inner.is_zero() {
            None
        } else {
            Some(NonZero(inner))
        }
    }

    /// Gets the inner value.
    pub fn get(self) -> T {
        self.0
    }
}
