//! Implements repetition of `Element`s.
use crate::base::{Element, Rec};

macro_rules! rpt {
    ($elmt:expr, $rep:expr) => {
        format!("{}{}", $elmt.to_group(), $rep).to_rec()
    };
}

macro_rules! num_rpt {
    ($elmt:expr, $count:expr) => {
        format!("{}{{{}}}", $elmt.to_group(), $count).to_rec()
    };
    ($elmt:expr, $min:expr, $max:expr) => {
        format!("{}{{{},{}}}", $elmt.to_group(), $min, $max).to_rec()
    };
    ($elmt:expr, $min:expr, $max:expr, $lazy:expr) => {
        format!("{}{{{},{}}}?", $elmt.to_group(), $min, $max).to_rec()
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
/// use rec::{var, Element, Rec};
///
/// assert_eq!(var('x'), Rec::from("x*"));
/// ```
#[inline]
pub fn var<T: Element>(element: T) -> Rec {
    rpt!(element, "*")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or more of times.
///
/// # Examples
/// ```
/// use rec::{lazy_var, Element, Rec};
///
/// assert_eq!(lazy_var('x'), Rec::from("x*?"));
/// ```
#[inline]
pub fn lazy_var<T: Element>(element: T) -> Rec {
    rpt!(element, "*?")
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::{some, Element, Rec};
///
/// assert_eq!(some('x'), Rec::from("x+"));
/// ```
#[inline]
pub fn some<T: Element>(element: T) -> Rec {
    rpt!(element, "+")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::{lazy_some, Element, Rec};
///
/// assert_eq!(lazy_some('x'), Rec::from("x+?"));
/// ```
#[inline]
pub fn lazy_some<T: Element>(element: T) -> Rec {
    rpt!(element, "+?")
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::{opt, Element, Rec};
///
/// assert_eq!(opt('x'), Rec::from("x?"));
/// ```
#[inline]
pub fn opt<T: Element>(element: T) -> Rec {
    rpt!(element, "?")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::{lazy_opt, Element, Rec};
///
/// assert_eq!(lazy_opt('x'), Rec::from("x??"));
/// ```
#[inline]
pub fn lazy_opt<T: Element>(element: T) -> Rec {
    rpt!(element, "??")
}

/// Returns a [`Rec`] representing the given [`Element`] repeated a given number of times.
///
/// # Examples
/// ```
/// use rec::{exact, Element, Rec};
///
/// assert_eq!(exact(3, 'x'), Rec::from("x{3}"));
/// ```
#[inline]
pub fn exact<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::{min, Element, Rec};
///
/// assert_eq!(min(2, 'x'), Rec::from("x{2,}"));
/// ```
#[inline]
pub fn min<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity, INFINITY)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::{lazy_min, Element, Rec};
///
/// assert_eq!(lazy_min(2, 'x'), Rec::from("x{2,}?"));
/// ```
#[inline]
pub fn lazy_min<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity, INFINITY, true)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated at most a given number of times.
///
/// # Examples
/// ```
/// use rec::{max, Element, Rec};
///
/// assert_eq!(max(4, 'x'), Rec::from("x{0,4}"));
/// ```
///
/// ```
/// use rec::{max, Class, Element, Pattern};
///
/// let pattern = Pattern::new(Class::Start + max(3, Class::Digit) + Class::End);
///
/// assert!(pattern.is_match("123"));
/// assert!(!pattern.is_match("1234"));
/// ```
pub fn max<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, ZERO, quantity)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated at most a given number of
/// times.
///
/// # Examples
/// ```
/// use rec::{lazy_max, Element, Rec};
///
/// assert_eq!(lazy_max(5, 'x'), Rec::from("x{0,5}?"));
/// ```
pub fn lazy_max<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, ZERO, quantity, true)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated between 2 numbers.
///
/// # Examples
/// ```
/// use rec::{btwn, Element, Rec};
///
/// assert_eq!(btwn(4, 7, 'x'), Rec::from("x{4,7}"));
/// ```
#[inline]
pub fn btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    num_rpt!(element, min, max)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated a range of given times.
///
/// # Examples
/// ```
/// use rec::{lazy_btwn, Element, Rec};
///
/// assert_eq!(lazy_btwn(4, 7, 'x'), Rec::from("x{4,7}?"));
/// ```
#[inline]
pub fn lazy_btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    num_rpt!(element, min, max, true)
}
