use rec::rec;

#[test]
fn text_start() {
    #[rec]
    const TEXT_START: Rec = text::START;
    assert_eq!(TEXT_START, r"\A");
}

#[test]
fn text_end() {
    #[rec]
    const TEXT_END: Rec = text::END;
    assert_eq!(TEXT_END, r"\z");
}
