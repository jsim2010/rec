use rec::rec;

rec! {text_start_re = text::START}
rec! {text_end_re = text::END}

#[test]
fn text_start() {
    assert_eq!(text_start_re(), r"\A");
}

#[test]
fn text_end() {
    assert_eq!(text_end_re(), r"\z");
}
