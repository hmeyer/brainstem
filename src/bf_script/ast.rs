use std::fmt::{Debug, Error, Formatter};

pub enum Statement<'input> {
    VarDeclaration(&'input str, Vec<Expression<'input>>),
    If(Expression<'input>, Box<Statement<'input>>),
    PutChar(Expression<'input>),
    While(Expression<'input>, Box<Statement<'input>>),
    Block(Vec<Statement<'input>>),
    Expression(Expression<'input>),
}

impl Debug for Statement<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        use self::Statement::*;
        match *self {
            VarDeclaration(n, ref i) => {
                if i.len() == 1 {
                    write!(fmt, "var {} = {:?};", n, i[0])
                } else {
                    write!(fmt, "var {}[] = {:?};", n, i)
                }
            }
            If(ref c, ref s) => write!(fmt, "if ({:?}) then {:?};", c, s),
            PutChar(ref e) => write!(fmt, "putchar({:?});", e),
            While(ref c, ref s) => write!(fmt, "while ({:?}) do {:?};", c, s),
            Block(ref v) => {
                writeln!(fmt, "{{")?;
                for s in v {
                    writeln!(fmt, "{:?}", s)?;
                }
                writeln!(fmt, "}}")
            }
            Expression(ref e) => write!(fmt, "{:?};", e),
        }
    }
}

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
    Mod,
    Add,
    Sub,
    Not,
    And,
    Or,
    Xor,
    Gt,
    Ge,
    Lt,
    Le,
    Eq,
    Ne,
}

impl From<&str> for Opcode {
    fn from(op: &str) -> Self {
        match op {
            "*" => Opcode::Mul,
            "/" => Opcode::Div,
            "%" => Opcode::Mod,
            "+" => Opcode::Add,
            "-" => Opcode::Sub,
            "&" => Opcode::And,
            "|" => Opcode::Or,
            "^" => Opcode::Xor,
            "!" => Opcode::Not,
            ">" => Opcode::Gt,
            ">=" => Opcode::Ge,
            "<" => Opcode::Lt,
            "<=" => Opcode::Le,
            "==" => Opcode::Eq,
            "!=" => Opcode::Ne,
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
            Mod => write!(fmt, "%"),
            Add => write!(fmt, "+"),
            Sub => write!(fmt, "-"),
            Not => write!(fmt, "-"),
            And => write!(fmt, "&"),
            Or => write!(fmt, "|"),
            Xor => write!(fmt, "^"),
            Gt => write!(fmt, ">"),
            Ge => write!(fmt, ">="),
            Lt => write!(fmt, "<"),
            Le => write!(fmt, "<="),
            Eq => write!(fmt, "=="),
            Ne => write!(fmt, "!="),
        }
    }
}
