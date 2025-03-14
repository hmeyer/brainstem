#[derive(Debug)]
pub enum Op {
    MovePointer(isize),
    AddValue(i32),
    JumpIfNotZero(usize),
    JumpBack(isize),
    Read,
    Write,
    SetToZero,
}

pub fn match_jumps(mut program: Vec<Op>) -> Result<Vec<Op>, &'static str> {
    let mut jumps = Vec::new();
    for i in 0..program.len() {
        match program[i] {
            Op::JumpIfNotZero(_) => jumps.push(i),
            Op::JumpBack(_) => {
                if jumps.is_empty() {
                    return Err("Unmatched ']'");
                }
                let jnz = jumps.pop().unwrap();
                program[jnz] = Op::JumpIfNotZero(i);
                program[i] = Op::JumpBack(jnz as isize - 1);
            }
            _ => (),
        }
    }
    if jumps.is_empty() {
        Ok(program)
    } else {
        Err("Unmatched '['")
    }
}
