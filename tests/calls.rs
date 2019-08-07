use rec::rec;

#[test]
fn call_other_rec() {
    #[rec]
    const CALLEE: Rec = '0'..'9';
    #[rec]
    const CALLER: Rec = "test" + crate::CALLEE;
    assert_eq!(CALLER, "test[0-9]");
}
