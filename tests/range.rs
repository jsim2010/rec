use rec::rec;

#[test]
fn char_range() {
    #[rec]
    const REC: Rec = 'a'..'z';
    assert_eq!(REC.to_string(), "[a-z]");
}
