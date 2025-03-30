mod ast;
mod runtime;

use anyhow::Result;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/bf_script/bf_script.rs");

#[cfg(test)]
mod tests {
    use super::parser::ProgramParser;

    #[test]
    fn literal_expressions() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new().parse(r#"3;"a";"#).unwrap()
            ),
            "[3;, 97;]"
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
    fn if_statement() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new()
                    .parse("if x then { var y = 2; } else { var z = 3; }")
                    .unwrap()
            ),
            "[if x then {\nvar y = 2;\n} else {\nvar z = 3;\n};]"
        );
    }

    #[test]
    fn if_nested() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new()
                    .parse("if (x) then { if (y) then { 2; } } else { var z = 3; }")
                    .unwrap()
            ),
            "[if x then {\nif y then {\n2;\n};\n} else {\nvar z = 3;\n};]"
        );
    }

    #[test]
    fn putc() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new().parse("putc(foo + bar);").unwrap()
            ),
            "[putc((foo + bar));]"
        );
    }

    #[test]
    fn test_while() {
        assert_eq!(
            format!(
                "{:?}",
                ProgramParser::new()
                    .parse("while foo / bar { x; }")
                    .unwrap()
            ),
            "[while ((foo / bar)) {\nx;\n}]"
        );
    }
}
