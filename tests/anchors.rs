use rec::rec;

#[test]
fn text_start() {
    #[rec]
    const TEXT_START: Rec = anchor::TEXT_START;
    assert_eq!(TEXT_START, r"\A");
}

#[test]
fn text_end() {
    #[rec]
    const TEXT_END: Rec = anchor::TEXT_END;
    assert_eq!(TEXT_END, r"\z");
}
