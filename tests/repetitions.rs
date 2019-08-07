use rec::rec;

#[test]
fn repeat_zero_or_more() {
    #[rec]
    const ZERO_OR_MORE: Rec = ['x'; ..];
    assert_eq!(ZERO_OR_MORE, "x*");
}

#[test]
fn lazy_repeat_zero_or_more() {
    #[rec]
    const LAZY_ZERO_OR_MORE: Rec = ['x'; lazy(..)];
    assert_eq!(LAZY_ZERO_OR_MORE, "x*?");
}

#[test]
fn repeat_one_or_more() {
    #[rec]
    const ONE_OR_MORE: Rec = ['x'; 1..];
    assert_eq!(ONE_OR_MORE, "x+");
}

#[test]
fn lazy_repeat_one_or_more() {
    #[rec]
    const LAZY_ONE_OR_MORE: Rec = ['x'; lazy(1..)];
    assert_eq!(LAZY_ONE_OR_MORE, "x+?");
}

#[test]
fn repeat_zero_or_one() {
    #[rec]
    const ZERO_OR_ONE: Rec = ['x'; ..=1];
    assert_eq!(ZERO_OR_ONE, "x?");
}

#[test]
fn lazy_repeat_zero_or_one() {
    #[rec]
    const LAZY_ZERO_OR_ONE: Rec = ['x'; lazy(..=1)];
    assert_eq!(LAZY_ZERO_OR_ONE, "x??");
}

#[test]
fn repeat_at_least_and_at_most() {
    #[rec]
    const RANGE: Rec = ['x'; 3..=5];
    assert_eq!(RANGE, "x{3,5}");
}

#[test]
fn lazy_repeat_at_least_and_at_most() {
    #[rec]
    const LAZY_RANGE: Rec = ['x'; lazy(3..=5)];
    assert_eq!(LAZY_RANGE, "x{3,5}?");
}

#[test]
fn repeat_at_least() {
    #[rec]
    const AT_LEAST: Rec = ['x'; 2..];
    assert_eq!(AT_LEAST, "x{2,}");
}

#[test]
fn lazy_repeat_at_least() {
    #[rec]
    const LAZY_AT_LEAST: Rec = ['x'; lazy(2..)];
    assert_eq!(LAZY_AT_LEAST, "x{2,}?");
}

#[test]
fn repeat_at_most() {
    #[rec]
    const AT_MOST: Rec = ['x'; 0..=4];
    assert_eq!(AT_MOST, "x{0,4}");
}

#[test]
fn lazy_repeat_at_most() {
    #[rec]
    const LAZY_AT_MOST: Rec = ['x'; lazy(0..=4)];
    assert_eq!(LAZY_AT_MOST, "x{0,4}?");
}

#[test]
fn repeat_exact() {
    #[rec]
    const EXACT: Rec = ['x'; 3];
    assert_eq!(EXACT, "x{3}");
}
