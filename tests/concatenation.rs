use rec::rec;

#[test]
fn single_plus() {
    #[rec]
    const SINGLE_PLUS: Rec = 'a' + 'b';
    assert_eq!(SINGLE_PLUS, "ab");
}

#[test]
fn multiple_plus() {
    #[rec]
    const MULTIPLE_PLUS: Rec = 'a' + "test" + ('0'..'9') + 'z';
    assert_eq!(MULTIPLE_PLUS, "atest[0-9]z")
}
