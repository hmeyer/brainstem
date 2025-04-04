use std::fmt::{Debug, Error, Formatter};

pub enum Statement<'input> {
    VarDeclaration(&'input str, Expression<'input>),
    ArrayDeclaration(&'input str, Vec<Expression<'input>>),
    If(
        Expression<'input>,
        Box<Statement<'input>>,
        Option<Box<Statement<'input>>>,
    ),
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
                write!(fmt, "var {} = {:?};", n, i)
            }
            ArrayDeclaration(n, ref i) => {
                let initializers = i
                    .iter()
                    .map(|e| format!("{:?}", e))
                    .collect::<Vec<_>>()
                    .join("; ");
                write!(fmt, "ArrayDeclaration({}; ({}));", n, initializers)
            }
            If(ref c, ref t, ref e) => match e {
                Some(e) => write!(fmt, "if {:?} then {:?} else {:?};", c, t, e),
                None => write!(fmt, "if {:?} then {:?};", c, t),
            },
            PutChar(ref e) => write!(fmt, "putc({:?});", e),
            While(ref c, ref s) => write!(fmt, "while ({:?}) {:?}", c, s),
            Block(ref v) => {
                writeln!(fmt, "{{")?;
                for s in v {
                    writeln!(fmt, "{:?}", s)?;
                }
                write!(fmt, "}}")
            }
            Expression(ref e) => write!(fmt, "{:?};", e),
        }
    }
}

#[derive(Clone)]
pub enum Expression<'input> {
    Literal(i32),
    Not(Box<Expression<'input>>),
    Binary(Box<Expression<'input>>, Opcode, Box<Expression<'input>>),
    Variable(&'input str),
    ArrayLookup(&'input str, Box<Expression<'input>>),
    Assignment(&'input str, Box<Expression<'input>>),
    ArrayAssignment(
        &'input str,
        Box<Expression<'input>>,
        Box<Expression<'input>>,
    ),
    MemoryRead(Box<Expression<'input>>),
    MemoryWrite(Box<Expression<'input>>, Box<Expression<'input>>),
}

#[derive(Copy, Clone)]
pub enum Opcode {
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    And,
    Or,
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
            "&&" => Opcode::And,
            "||" => Opcode::Or,
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
            Not(ref e) => write!(fmt, "!{:?}", e),
            Binary(ref l, op, ref r) => write!(fmt, "({:?} {:?} {:?})", l, op, r),
            Variable(s) => write!(fmt, "{}", s),
            ArrayLookup(s, ref i) => write!(fmt, "ArrayLookup({}; {:?})", s, i),
            Assignment(s, ref e) => write!(fmt, "{} = {:?}", s, e),
            ArrayAssignment(s, ref i, ref e) => {
                write!(fmt, "ArrayAssignment({}; {:?}; {:?})", s, i, e)
            }
            MemoryRead(ref e) => write!(fmt, "MemoryRead(addr={:?})", e),
            MemoryWrite(ref a, ref e) => write!(fmt, "MemoryWrite(addr={:?}; value={:?})", a, e),
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
            Add => write!(fmt, "➕"),
            Sub => write!(fmt, "➖"),
            And => write!(fmt, "&&"),
            Or => write!(fmt, "||"),
            Lt => write!(fmt, "lt"),
            Le => write!(fmt, "le"),
            Eq => write!(fmt, "=="),
            Ne => write!(fmt, "!="),
        }
    }
}
