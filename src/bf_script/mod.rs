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
                    .parse("var multi[] = \"Foo\";")
                    .unwrap()
            ),
            "[var multi[] = [70, 111, 111];]"
        );
    }

    #[test]
    fn unary_expressions() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new().parse("var x = !--+3;").unwrap()
            ),
            "[var x = !--3;]"
        );
    }

    #[test]
    fn muliplication_expressions() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new().parse("var x = 3 * 4 * foo;").unwrap()
            ),
            "[var x = ((3 * 4) * foo);]"
        );
    }

    #[test]
    fn arithmetic_expressions() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new().parse("var x = 3 + 4 * foo;").unwrap()
            ),
            "[var x = (3 + (4 * foo));]"
        );
    }

    #[test]
    fn logic_expressions() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new()
                    .parse("var x = !foo && bar || 2;")
                    .unwrap()
            ),
            "[var x = ((!foo && bar) || 2);]"
        );
    }

    #[test]
    fn equality_expressions() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new().parse("var x = 2 == 3 != 4;").unwrap()
            ),
            "[var x = ((2 == 3) != 4);]"
        );
    }

    #[test]
    fn complex_expressions() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new()
                    .parse("var x = 1 + 2 * 3 || 4 > (3 + 2) - !foo;")
                    .unwrap()
            ),
            "[var x = ((1 + (2 * 3)) || (4 > ((3 + 2) - !foo)));]"
        );
    }
}
