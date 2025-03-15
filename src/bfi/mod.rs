mod ast;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(parser, "/bfi/bf.rs");

#[cfg(test)]
mod tests {
    use super::parser::ProgramParser;

    #[test]
    fn moves() {
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse(">").unwrap()),
            "[MovePointer(1)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse(">>").unwrap()),
            "[MovePointer(2)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("<").unwrap()),
            "[MovePointer(-1)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("<<<").unwrap()),
            "[MovePointer(-3)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse(">><<<").unwrap()),
            "[MovePointer(-1)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("<>").unwrap()),
            "[]"
        );
    }

    #[test]
    fn increments() {
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("+").unwrap()),
            "[Increment(1)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("++").unwrap()),
            "[Increment(2)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("-").unwrap()),
            "[Increment(-1)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("---").unwrap()),
            "[Increment(-3)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("+-+-+").unwrap()),
            "[Increment(1)]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("+-").unwrap()),
            "[]"
        );
    }

    #[test]
    fn zero() {
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("[-]").unwrap()),
            "[SetToZero]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("++++[-]").unwrap()),
            "[SetToZero]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("----[-]").unwrap()),
            "[SetToZero]"
        );
        assert_eq!(
            &format!(
                "{:?}",
                ProgramParser::new().parse("+>-+<-+[-+-+-]").unwrap()
            ),
            "[SetToZero]"
        );
    }

    #[test]
    fn io() {
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse(",").unwrap()),
            "[Read]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse(".").unwrap()),
            "[Write]"
        );
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse(".,.,").unwrap()),
            "[Write, Read, Write, Read]"
        );
    }

    #[test]
    fn loops() {
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("[]").unwrap()),
            "[JumpIfNotZero(1), JumpBack(-1)]"
        );
        assert!(ProgramParser::new().parse("[").is_err());
        assert!(ProgramParser::new().parse("]").is_err());
    }

    #[test]
    fn compact() {
        assert_eq!(
            &format!("{:?}", ProgramParser::new().parse("+<>-").unwrap()),
            "[]"
        );
    }

    #[test]
    fn non_bf_and_comments() {
        assert_eq!(
            &format!(
                "{:?}",
                ProgramParser::new()
                    .parse(
                        "This is a comment Then move right >
            then a line break: left: <
            + & -
            zero:[With-Comments]
            done"
                    )
                    .unwrap()
            ),
            "[SetToZero]"
        );
    }
}
