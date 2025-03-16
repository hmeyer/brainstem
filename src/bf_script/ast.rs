use std::fmt::{Debug, Error, Formatter};

pub enum Expression<'input> {
    Literal(i32),
    Unary(Opcode, Box<Expression<'input>>),
    Binary(Box<Expression<'input>>, Opcode, Box<Expression<'input>>),
    Variable(&'input str),
    IndexedVariable(&'input str, Box<Expression<'input>>),
    Assignment(&'input str, Box<Expression<'input>>),
    IndexedAssignment(
        &'input str,
        Box<Expression<'input>>,
        Box<Expression<'input>>,
    ),
}

#[derive(Copy, Clone)]
pub enum Opcode {
    Mul,
    Div,
    Add,
    Sub,
    Not,
    And,
    Or,
    Xor,
}

impl From<&str> for Opcode {
    fn from(op: &str) -> Self {
        match op {
            "*" => Opcode::Mul,
            "/" => Opcode::Div,
            "+" => Opcode::Add,
            "-" => Opcode::Sub,
            "&" => Opcode::And,
            "|" => Opcode::Or,
            "^" => Opcode::Xor,
            _ => panic!("Unsupported operator: {}", op),
        }
    }
}

impl Debug for Expression<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        use self::Expression::*;
        match *self {
            Literal(n) => write!(fmt, "{}", n),
            Unary(op, ref e) => write!(fmt, "({:?}{:?})", op, e),
            Binary(ref l, op, ref r) => write!(fmt, "({:?} {:?} {:?})", l, op, r),
            Variable(s) => write!(fmt, "{}", s),
            IndexedVariable(s, ref e) => write!(fmt, "{}[{:?}]", s, e),
            Assignment(s, ref e) => write!(fmt, "{} = {:?}", s, e),
            IndexedAssignment(s, ref i, ref e) => write!(fmt, "{}[{:?}] = {:?}", s, i, e),
        }
    }
}

impl Debug for Opcode {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        use self::Opcode::*;
        match *self {
            Mul => write!(fmt, "*"),
            Div => write!(fmt, "/"),
            Add => write!(fmt, "+"),
            Sub => write!(fmt, "-"),
            Not => write!(fmt, "-"),
            And => write!(fmt, "&"),
            Or => write!(fmt, "|"),
            Xor => write!(fmt, "^"),
        }
    }
}
