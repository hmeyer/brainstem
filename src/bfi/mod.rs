mod ast;

use anyhow::Result;
use ast::Op;
use lalrpop_util::lalrpop_mod;
use num_traits::{FromPrimitive, PrimInt, ToPrimitive, WrappingAdd, WrappingSub};
use std::collections::HashMap;
use std::fmt::Debug;
use std::io::{Cursor, Read, Write};

lalrpop_mod!(parser, "/bfi/bf.rs");

pub fn run_program<T>(
    program: &str,
    input: &mut impl Read,
    output: &mut impl Write,
    max_steps: Option<usize>,
) -> Result<usize>
where
    T: PrimInt + FromPrimitive + ToPrimitive + WrappingSub + WrappingAdd + Debug,
{
    let ops = parser::ProgramParser::new()
        .parse(program)
        .map_err(|e| anyhow::anyhow!("{}", e))?;
    let mut memory: HashMap<isize, T> = HashMap::new();
    let mut ip: usize = 0;
    let mut mp: isize = 0;
    let mut steps = 0;
    let zero = T::zero();
    while ip < ops.len() && (max_steps.is_none() || steps < max_steps.unwrap()) {
        let op = &ops[ip];
        ip += 1;
        steps += 1;
        match op {
            Op::MovePointer(n) => {
                mp += n;
            }
            Op::Increment(n) => {
                let cell = memory.entry(mp).or_insert(T::zero());
                if *n < 0 {
                    let decrement = T::from_i32(-*n).ok_or_else(|| {
                        anyhow::anyhow!(
                            "Conversion error: could not convert decrement value {} to target type",
                            n
                        )
                    })?;
                    *cell = cell.wrapping_sub(&decrement);
                } else {
                    let increment = T::from_i32(*n).ok_or_else(|| {
                        anyhow::anyhow!(
                            "Conversion error: could not convert increment value {} to target type",
                            n
                        )
                    })?;
                    *cell = cell.wrapping_add(&increment);
                }
            }
            Op::Read => {
                let mut buf = [0; 1];
                let len = input.read(&mut buf)?;
                if len == 1 {
                    memory.insert(
                        mp,
                        T::from_u8(buf[0]).ok_or_else(|| {
                            anyhow::anyhow!("Conversion error from u8 to target type")
                        })?,
                    );
                } else {
                    // EOF: insert -1 into memory
                    memory.insert(
                        mp,
                        T::from_i32(-1).ok_or_else(|| {
                            anyhow::anyhow!("Conversion error from i32 to target type")
                        })?,
                    );
                }
            }
            Op::Write => {
                let cell = memory.get(&mp).unwrap_or(&zero);
                let value = cell
                    .clone()
                    .to_u8()
                    .ok_or_else(|| anyhow::anyhow!("Could not convert {:?} to u8", cell))?;
                output.write_all(&[value])?;
            }
            Op::JumpIfZero(n) => {
                if memory.get(&mp).unwrap_or(&zero) == &zero {
                    ip = *n;
                }
            }
            Op::JumpBack(n) => {
                ip = *n;
            }
            Op::SetToZero => {
                memory.insert(mp, T::zero());
            }
        }
    }
    if ip < ops.len() {
        return Err(anyhow::anyhow!("max_steps {} exceeded", steps));
    }
    Ok(steps)
}

pub fn run_program_from_str<T>(
    program: &str,
    input: &str,
    max_steps: Option<usize>,
) -> Result<String>
where
    T: PrimInt + FromPrimitive + ToPrimitive + WrappingSub + WrappingAdd + Debug,
{
    let mut reader = Cursor::new(input.as_bytes());
    let mut output_buffer = Vec::new();
    let mut writer = Cursor::new(&mut output_buffer);
    run_program::<T>(program, &mut reader, &mut writer, max_steps).map_err(|e| {
        // Get any output that was produced before the error
        let partial_output = output_buffer.iter().map(|&c| c as char).collect::<String>();
        anyhow::anyhow!("Error: {}. Partial output: {}", e, partial_output)
    })?;
    Ok(output_buffer.iter().map(|&c| c as char).collect::<String>())
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
        assert_eq!(run_program_from_str::<i32>("++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.+++++++..+++.>++.<<+++++++++++++++.>.+++.------.--------.>+.>.", "", Some(1000)).unwrap(), "Hello World!\n");
    }

    #[test]
    fn run_rot13() {
        assert_eq!(run_program_from_str::<i32>(r"#
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
        assert!(
            run_program::<i32>("[", &mut std::io::empty(), &mut std::io::empty(), None).is_err()
        );
    }
}
