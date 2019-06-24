//! Implements repetition of `Element`s.
use crate::prelude::*;

macro_rules! rpt {
    ($elmt:expr, $rep:expr) => {
        Rec::from(format!("{}{}", $elmt.group(), $rep))
    };
}

macro_rules! num_rpt {
    ($elmt:expr, $count:expr) => {
        Rec::from(format!("{}{{{}}}", $elmt.group(), $count))
    };
    ($elmt:expr, $min:expr, $max:expr) => {
        Rec::from(format!("{}{{{},{}}}", $elmt.group(), $min, $max))
    };
    ($elmt:expr, $min:expr, $max:expr, $lazy:expr) => {
        Rec::from(format!("{}{{{},{}}}?", $elmt.group(), $min, $max))
    };
}

/// Signifies a minimum value of zero in a quantifier.
const ZERO: &str = "0";
/// Signifies a maximum value of infinity in a quantifier.
const INFINITY: &str = "";

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 0 or more times.
///
/// # Examples
/// ```
/// use rec::{prelude::*, var};
///
/// assert_eq!(var('x'), Rec::from("x*"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn var<T: Element>(element: T) -> Rec {
    rpt!(element, "*")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or more of times.
///
/// # Examples
/// ```
/// use rec::{lazy_var, prelude::*};
///
/// assert_eq!(lazy_var('x'), Rec::from("x*?"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn lazy_var<T: Element>(element: T) -> Rec {
    rpt!(element, "*?")
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::{prelude::*, some};
///
/// assert_eq!(some('x'), Rec::from("x+"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn some<T: Element>(element: T) -> Rec {
    rpt!(element, "+")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::{lazy_some, prelude::*};
///
/// assert_eq!(lazy_some('x'), Rec::from("x+?"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn lazy_some<T: Element>(element: T) -> Rec {
    rpt!(element, "+?")
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::{opt, prelude::*};
///
/// assert_eq!(opt('x'), Rec::from("x?"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn opt<T: Element>(element: T) -> Rec {
    rpt!(element, "?")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::{lazy_opt, prelude::*};
///
/// assert_eq!(lazy_opt('x'), Rec::from("x??"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn lazy_opt<T: Element>(element: T) -> Rec {
    rpt!(element, "??")
}

/// Returns a [`Rec`] representing the given [`Element`] repeated a given number of times.
///
/// # Examples
/// ```
/// use rec::{exact, prelude::*};
///
/// assert_eq!(exact(3, 'x'), Rec::from("x{3}"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn exact<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::{min, prelude::*};
///
/// assert_eq!(min(2, 'x'), Rec::from("x{2,}"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn min<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity, INFINITY)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::{lazy_min, prelude::*};
///
/// assert_eq!(lazy_min(2, 'x'), Rec::from("x{2,}?"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn lazy_min<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity, INFINITY, true)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated at most a given number of times.
///
/// # Examples
/// ```
/// use rec::{max, prelude::*};
///
/// assert_eq!(max(4, 'x'), Rec::from("x{0,4}"));
/// ```
///
/// ```
/// use rec::{max, Class, prelude::*, Pattern};
///
/// let pattern = Pattern::new(Class::Start + max(3, Class::Digit) + Class::End);
///
/// assert!(pattern.is_match("123"));
/// assert!(!pattern.is_match("1234"));
/// ```
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn max<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, ZERO, quantity)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated at most a given number of
/// times.
///
/// # Examples
/// ```
/// use rec::{lazy_max, prelude::*};
///
/// assert_eq!(lazy_max(5, 'x'), Rec::from("x{0,5}?"));
/// ```
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn lazy_max<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, ZERO, quantity, true)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated between 2 numbers.
///
/// # Examples
/// ```
/// use rec::{btwn, prelude::*};
///
/// assert_eq!(btwn(4, 7, 'x'), Rec::from("x{4,7}"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    num_rpt!(element, min, max)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated a range of given times.
///
/// # Examples
/// ```
/// use rec::{lazy_btwn, prelude::*};
///
/// assert_eq!(lazy_btwn(4, 7, 'x'), Rec::from("x{4,7}?"));
/// ```
#[inline]
#[allow(clippy::needless_pass_by_value)] // User interface is much better when passing by value.
pub fn lazy_btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    num_rpt!(element, min, max, true)
}
