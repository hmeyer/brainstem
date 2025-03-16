mod ast;

use anyhow::Result;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/bf_script/bf_script.rs");


#[cfg(test)]
mod tests {
    use super::parser::ExpressionParser;

    #[test]
    fn calculator1() {
        assert_eq!(format!("{:?}", ExpressionParser::new().parse("22 + 12").unwrap()), "(22 + 12)");
        assert_eq!(format!("{:?}", ExpressionParser::new().parse("22 + 12 * 3").unwrap()), "(22 + (12 * 3))");
    }

}