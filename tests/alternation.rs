use rec::rec;

#[test]
fn char_or_str() {
    #[rec]
    const CHAR_OR_STR: Rec = 'a' | "xyz";
    assert_eq!(CHAR_OR_STR, r"a|xyz");
}

#[test]
fn str_or_range() {
    #[rec]
    const STR_OR_RANGE: Rec = "abc" | ('x'..'z');
    assert_eq!(STR_OR_RANGE, r"abc|[x-z]");
}
