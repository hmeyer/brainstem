/// Basic Brainfuck Operations.
#[derive(Debug, Copy, Clone)]
pub enum Op {
    /// Move the pointer to the right by n cells - corresponds to '>' and '<'.
    MovePointer(isize),
    /// Increment the value at the current cell by n - corresponds to '+' and '-'.
    Increment(i32),
    /// Jump to the instruction after the matching ']' if the current cell is zero - corresponds to '['.
    JumpIfNotZero(usize),
    /// Jump back to the instruction after the matching '[' if the current cell is not zero - corresponds to ']'.
    JumpBack(isize),
    /// Read a byte from the standard input and store it in the current cell - corresponds to ','.
    Read,
    /// Write the byte at the current cell to the standard output - corresponds to '.'.
    Write,
    /// Set the value at the current cell to zero - corresponds to '[-]'.
    SetToZero,
}

/// Compact the program by combining consecutive MovePointer and Increment operations.
fn compact(mut program: Vec<Op>) -> Vec<Op> {
    let mut compacted;
    while !program.is_empty() {
        compacted = Vec::new();
        let mut previous_op = program[0];
        for op in program.iter().skip(1) {
            match (previous_op, op) {
                (Op::MovePointer(n), Op::MovePointer(m)) => {
                    previous_op = Op::MovePointer(n + m);
                }
                (Op::Increment(n), Op::Increment(m)) => {
                    previous_op = Op::Increment(n + m);
                }
                _ => {
                    match previous_op {
                        Op::MovePointer(0) | Op::Increment(0) => (),
                        _ => compacted.push(previous_op),
                    }
                    previous_op = *op;
                }
            }
        }
        match previous_op {
            Op::MovePointer(0) | Op::Increment(0) => (),
            _ => compacted.push(previous_op),
        }
        if compacted.len() == program.len() {
            break;
        }
        program = compacted;
    }
    program
}

/// Find set to zero operations and replace them with SetToZero.
fn optimize_set_to_zero(mut program: Vec<Op>) -> Vec<Op> {
    let mut i = 0;
    while i + 2 < program.len() {
        match program[i..i + 3] {
            [Op::JumpIfNotZero(_), Op::Increment(-1), Op::JumpBack(_)] => {
                program[i] = Op::SetToZero;
                program.remove(i + 1);
                program.remove(i + 1);
            }
            _ => i += 1,
        }
    }
    // Remove any Increment operations that are followed by SetToZero.
    i = 0;
    while i + 1 < program.len() {
        match program[i..i + 2] {
            [Op::Increment(_), Op::SetToZero] => {
                program[i] = Op::SetToZero;
                program.remove(i + 1);
            }
            _ => i += 1,
        }
    }
    program
}

/// Match jumps and populates the JumpIfNotZero and JumpBack operations.
fn match_jumps(mut program: Vec<Op>) -> Result<Vec<Op>, &'static str> {
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

/// Finalize the program by compacting, optimizing set to zero, and matching jumps.
pub fn finalize(program: Vec<Op>) -> Result<Vec<Op>, &'static str> {
    let program = compact(program);
    let program = optimize_set_to_zero(program);
    match_jumps(program)
}
