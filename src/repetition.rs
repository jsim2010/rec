//! Implements repetition of `Element`s.
use crate::base::{Element, Rec};

macro_rules! rpt {
    ($elmt:expr, $rep:expr) => {
        format!("{}{}", $elmt.group(), $rep).into_rec()
    };
}

macro_rules! num_rpt {
    ($elmt:expr, $count:expr) => {
        format!("{}{{{}}}", $elmt.group(), $count).into_rec()
    };
    ($elmt:expr, $min:expr, $max:expr) => {
        format!("{}{{{},{}}}", $elmt.group(), $min, $max).into_rec()
    };
    ($elmt:expr, $min:expr, $max:expr, $lazy:expr) => {
        format!("{}{{{},{}}}?", $elmt.group(), $min, $max).into_rec()
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
/// use rec::{var, Element};
///
/// assert_eq!(var("x"), String::from("x*").into_rec());
/// ```
#[inline]
pub fn var<T: Element>(element: T) -> Rec {
    rpt!(element, "*")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or more of times.
///
/// # Examples
/// ```
/// use rec::{lazy_var, Element};
///
/// assert_eq!(lazy_var("x"), String::from("x*?").into_rec());
/// ```
#[inline]
pub fn lazy_var<T: Element>(element: T) -> Rec {
    rpt!(element, "*?")
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::{some, Element};
///
/// assert_eq!(some("x"), String::from("x+").into_rec());
/// ```
#[inline]
pub fn some<T: Element>(element: T) -> Rec {
    rpt!(element, "+")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 1 or more times.
///
/// # Examples
/// ```
/// use rec::{lazy_some, Element};
///
/// assert_eq!(lazy_some("x"), String::from("x+?").into_rec());
/// ```
#[inline]
pub fn lazy_some<T: Element>(element: T) -> Rec {
    rpt!(element, "+?")
}

/// Returns a [`Rec`] representing the given [`Element`] greedily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::{opt, Element};
///
/// assert_eq!(opt("x"), String::from("x?").into_rec());
/// ```
#[inline]
pub fn opt<T: Element>(element: T) -> Rec {
    rpt!(element, "?")
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated 0 or 1 times.
///
/// # Examples
/// ```
/// use rec::{lazy_opt, Element};
///
/// assert_eq!(lazy_opt("x"), String::from("x??").into_rec());
/// ```
#[inline]
pub fn lazy_opt<T: Element>(element: T) -> Rec {
    rpt!(element, "??")
}

/// Returns a [`Rec`] representing the given [`Element`] repeated a given number of times.
///
/// # Examples
/// ```
/// use rec::{exact, Element};
///
/// assert_eq!(exact(3, "x"), String::from("x{3}").into_rec());
/// ```
#[inline]
pub fn exact<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::{min, Element};
///
/// assert_eq!(min(2, "x"), String::from("x{2,}").into_rec());
/// ```
#[inline]
pub fn min<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity, INFINITY)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated at least a given number of times.
///
/// # Examples
/// ```
/// use rec::{lazy_min, Element};
///
/// assert_eq!(lazy_min(2, "x"), String::from("x{2,}?").into_rec());
/// ```
#[inline]
pub fn lazy_min<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, quantity, INFINITY, true)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated at most a given number of times.
///
/// # Examples
/// ```
/// use rec::{max, Element};
///
/// assert_eq!(max(4, "x"), String::from("x{0,4}").into_rec());
/// ```
///
/// ```
/// use rec::{max, Ch, Element, Pattern};
///
/// let pattern = Pattern::new(Ch::Start + max(3, Ch::Digit) + Ch::End);
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
/// use rec::{lazy_max, Element};
///
/// assert_eq!(lazy_max(5, "x"), String::from("x{0,5}?").into_rec());
/// ```
pub fn lazy_max<T: Element>(quantity: usize, element: T) -> Rec {
    num_rpt!(element, ZERO, quantity, true)
}

/// Returns a [`Rec`] representing the given [`Element`] repeated between 2 numbers.
///
/// # Examples
/// ```
/// use rec::{btwn, Element};
///
/// assert_eq!(btwn(4, 7, "x"), String::from("x{4,7}").into_rec());
/// ```
#[inline]
pub fn btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    num_rpt!(element, min, max)
}

/// Returns a [`Rec`] representing the given [`Element`] lazily repeated a range of given times.
///
/// # Examples
/// ```
/// use rec::{lazy_btwn, Element};
///
/// assert_eq!(lazy_btwn(4, 7, "x"), String::from("x{4,7}?").into_rec());
/// ```
#[inline]
pub fn lazy_btwn<T: Element>(min: usize, max: usize, element: T) -> Rec {
    num_rpt!(element, min, max, true)
}
