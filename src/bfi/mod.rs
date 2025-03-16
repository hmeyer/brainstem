mod ast;

use anyhow::Result;
use ast::Op;
use lalrpop_util::lalrpop_mod;
use std::collections::HashMap;
use std::io::{Cursor, Read, Write};

lalrpop_mod!(parser, "/bfi/bf.rs");

pub fn run_program(
    program: &str,
    input: &mut impl Read,
    output: &mut impl Write,
    max_steps: Option<usize>,
) -> Result<()> {
    let ops = parser::ProgramParser::new()
        .parse(program)
        .map_err(|e| anyhow::anyhow!(format!("{:}", e)))?;
    let mut memory = HashMap::new();
    let mut ip: usize = 0;
    let mut mp: isize = 0;
    let mut steps = 0;
    while ip < ops.len() && (max_steps.is_none() || steps < max_steps.unwrap()) {
        let op = &ops[ip];
        ip += 1;
        steps += 1;
        match op {
            Op::MovePointer(n) => {
                mp += n;
            }
            Op::Increment(n) => {
                let cell = memory.entry(mp).or_insert(0);
                *cell += *n;
            }
            Op::Read => {
                let mut buf = [0; 1];
                let len = input.read(&mut buf)?;
                if len == 1 {
                    memory.insert(mp, buf[0] as i32);
                } else {
                    // EOF
                    memory.insert(mp, -1);
                }
            }
            Op::Write => {
                let cell = memory.get(&mp).unwrap_or(&0);
                output.write_all(&[*cell as u8])?;
            }
            Op::JumpIfZero(n) => {
                if memory.get(&mp).unwrap_or(&0) == &0 {
                    ip = *n;
                }
            }
            Op::JumpBack(n) => {
                ip = *n;
            }
            Op::SetToZero => {
                memory.insert(mp, 0);
            }
        }
    }
    Ok(())
}

pub fn run_program_from_str(
    program: &str,
    input: &str,
    max_steps: Option<usize>,
) -> Result<String> {
    let mut reader = Cursor::new(input.as_bytes());
    let mut output_buffer = Vec::new();
    let mut writer = Cursor::new(&mut output_buffer);
    run_program(program, &mut reader, &mut writer, max_steps)?;
    Ok(String::from_utf8(output_buffer).unwrap())
}

#[cfg(test)]
mod tests {
    use crate::bfi::run_program_from_str;

    use super::parser::ProgramParser;
    use super::run_program;

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
            "[JumpIfZero(2), JumpBack(0)]"
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

    #[test]
    fn run_hello_world() {
        assert_eq!(run_program_from_str("++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.+++++++..+++.>++.<<+++++++++++++++.>.+++.------.--------.>+.>.", "", Some(1000)).unwrap(), "Hello World!\n");
    }

    #[test]
    fn run_rot13() {
        assert_eq!(run_program_from_str(r"#
From: Wikipedia/Brainfuck
-,+[                         Read first character and start outer character reading loop
    -[                       Skip forward if character is 0
        >>++++[>++++++++<-]  Set up divisor (32) for division loop
                               (MEMORY LAYOUT: dividend copy remainder divisor quotient zero zero)
        <+<-[                Set up dividend (x minus 1) and enter division loop
            >+>+>-[>>>]      Increase copy and remainder / reduce divisor / Normal case: skip forward
            <[[>+<-]>>+>]    Special case: move remainder back to divisor and increase quotient
            <<<<<-           Decrement dividend
        ]                    End division loop
    ]>>>[-]+                 End skip loop; zero former divisor and reuse space for a flag
    >--[-[<->+++[-]]]<[         Zero that flag unless quotient was 2 or 3; zero quotient; check flag
        ++++++++++++<[       If flag then set up divisor (13) for second division loop
                               (MEMORY LAYOUT: zero copy dividend divisor remainder quotient zero zero)
            >-[>+>>]         Reduce divisor; Normal case: increase remainder
            >[+[<+>-]>+>>]   Special case: increase remainder / move it back to divisor / increase quotient
            <<<<<-           Decrease dividend
        ]                    End division loop
        >>[<+>-]             Add remainder back to divisor to get a useful 13
        >[                   Skip forward if quotient was 0
            -[               Decrement quotient and skip forward if quotient was 1
                -<<[-]>>     Zero quotient and divisor if quotient was 2
            ]<<[<<->>-]>>    Zero divisor and subtract 13 from copy if quotient was 1
        ]<<[<<+>>-]          Zero divisor and add 13 to copy if quotient was 0
    ]                        End outer skip loop (jump to here if ((character minus 1)/32) was not 2 or 3)
    <[-]                     Clear remainder from first division if second division was skipped
    <.[-]                    Output ROT13ed character from copy and clear it
    <-,+                     Read next character
]                            End character reading loop 
            #", "Hello World!", Some(40_000)).unwrap(), "Uryyb Jbeyq!");
    }

    #[test]
    fn run_with_parse_error() {
        assert!(run_program("[", &mut std::io::empty(), &mut std::io::empty(), None).is_err());
    }
}
