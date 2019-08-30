use rec::rec;

/// A repetition with a range full shall repeat 0 or more times.
#[test]
fn repeat_zero_or_more() {
    #[rec]
    const ZERO_OR_MORE: Rec = ['x'; ..];
    assert_eq!(ZERO_OR_MORE, "x*");
}

/// A repetition with a lazy range full shall lazily repeat 0 or more times.
#[test]
fn lazy_repeat_zero_or_more() {
    #[rec]
    const LAZY_ZERO_OR_MORE: Rec = ['x'; lazy(..)];
    assert_eq!(LAZY_ZERO_OR_MORE, "x*?");
}

/// A repetition with a range from 1 shall repeat 1 or more times.
#[test]
fn repeat_one_or_more() {
    #[rec]
    const ONE_OR_MORE: Rec = ['x'; 1..];
    assert_eq!(ONE_OR_MORE, "x+");
}

/// A repetition with a lazy range from 1 shall lazily repeat 1 or more times.
#[test]
fn lazy_repeat_one_or_more() {
    #[rec]
    const LAZY_ONE_OR_MORE: Rec = ['x'; lazy(1..)];
    assert_eq!(LAZY_ONE_OR_MORE, "x+?");
}

/// A repetition with a range to inclusive 1 shall repeat 0 or 1 times.
#[test]
fn repeat_zero_or_one() {
    #[rec]
    const ZERO_OR_ONE: Rec = ['x'; ..=1];
    assert_eq!(ZERO_OR_ONE, "x?");
}

/// A repetition with a lazy range to inclusive 1 shall lazily repeat 0 or 1 times.
#[test]
fn lazy_repeat_zero_or_one() {
    #[rec]
    const LAZY_ZERO_OR_ONE: Rec = ['x'; lazy(..=1)];
    assert_eq!(LAZY_ZERO_OR_ONE, "x??");
}

/// A repetition with a range inclusive shall repeat a number of times within the given range.
#[test]
fn repeat_at_least_and_at_most() {
    #[rec]
    const RANGE: Rec = ['x'; 3..=5];
    assert_eq!(RANGE, "x{3,5}");
}

/// A repetition with a lazy range inclusive shall lazily repeat a number of times within the given
/// range.
#[test]
fn lazy_repeat_at_least_and_at_most() {
    #[rec]
    const LAZY_RANGE: Rec = ['x'; lazy(3..=5)];
    assert_eq!(LAZY_RANGE, "x{3,5}?");
}

/// A repetition with a range from a number greater than 1 shall repeat at least that number of
/// times.
#[test]
fn repeat_at_least() {
    #[rec]
    const AT_LEAST: Rec = ['x'; 2..];
    assert_eq!(AT_LEAST, "x{2,}");
}

/// A repetition with a lazy range from a number greater than 1 shall lazily repeat at least that
/// number of times.
#[test]
fn lazy_repeat_at_least() {
    #[rec]
    const LAZY_AT_LEAST: Rec = ['x'; lazy(2..)];
    assert_eq!(LAZY_AT_LEAST, "x{2,}?");
}

/// A repetition with a literal integer shall repeat that number of times.
#[test]
fn repeat_exact() {
    #[rec]
    const EXACT: Rec = ['x'; 3];
    assert_eq!(EXACT, "x{3}");
}

/// A repetition with a compound [`rec expression`] shall repeat the entire [`rec expression`] as
/// one item.
#[test]
fn repeat_compound_expr() {
    #[rec]
    const REPEAT_COMPOUND: Rec = ["compound"; ..];
    assert_eq!(REPEAT_COMPOUND, "(?:compound)*");
}
