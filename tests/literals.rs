use rec::rec;

#[test]
fn char() {
    #[rec]
    const CHAR: Rec = 'a';
    assert_eq!(CHAR, "a");
}

#[test]
fn str() {
    #[rec]
    const STR: Rec = "test";
    assert_eq!(STR, "test");
}
