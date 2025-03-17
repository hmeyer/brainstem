mod ast;

use anyhow::Result;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/bf_script/bf_script.rs");

#[cfg(test)]
mod tests {
    use super::parser::ProgramParser;

    #[test]
    fn var_declaration() {
        assert_eq!(
            format!("{:?}", ProgramParser::new().parse("var x = 2;").unwrap()),
            "[var x = 2;]"
        );
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new().parse("var foo = 8 * 3 + 9;").unwrap()
            ),
            "[var foo = ((8 * 3) + 9);]"
        );
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new()
                    .parse("var multi[] = [1, 2, 3];")
                    .unwrap()
            ),
            "[var multi[] = [1, 2, 3];]"
        );
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new()
                    .parse("var multi[] = \"foo\";")
                    .unwrap()
            ),
            "[var multi[] = [1, 2, 3];]"
        );
    }
}
