//! Integration tests for the brainstem library

#[test]
fn compile_and_run_brainstem() {
    let src = r#"var x = 2 + 2; putc("0" + x);"#;
    let bf = brainstem::compile_brain_stem(src).expect("compile");
    let mut output = Vec::new();
    let mut input = std::io::empty();
    let steps =
        brainstem::run_program::<u8>(&bf, &mut input, &mut output, Some(1000), true).expect("run");
    assert!(steps > 0);
    assert_eq!(output, b"4");
}
