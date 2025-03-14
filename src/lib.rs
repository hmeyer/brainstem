mod bf_script_ast;
use lalrpop_util::lalrpop_mod;
mod bfi;

macro_rules! lalrpop_mod_doc {
    ($vis:vis $name:ident) => {
        lalrpop_util::lalrpop_mod!(
            #[allow(clippy::ptr_arg)]
            #[allow(clippy::vec_box)]
            $vis $name);
    }
}

lalrpop_mod_doc!(pub bf_script);

#[test]
fn calculator1() {
    assert!(bf_script::TermParser::new().parse("22").is_ok());
}
