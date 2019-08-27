use rec::rec;

/// A bitwise OR expression with at least 1 sub-expression that is not a [`class expression`]
/// shall be converted to an alternation.
#[test]
fn alternation() {
    #[rec]
    const CHAR_OR_STR: &str = 'a' | "xyz";
    assert_eq!(CHAR_OR_STR, r"a|xyz");

    #[rec]
    const STR_OR_RANGE: &str = "abc" | ('x'..'z');
    assert_eq!(STR_OR_RANGE, r"abc|[x-z]");
}
