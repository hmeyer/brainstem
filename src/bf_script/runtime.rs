use super::{
    ast, context::AsVariableLikeRef, context::Context, context::ContextExt, context::Variable,
    context::VariableExt, context::VariableLike, parser::ProgramParser,
};
use anyhow::{Result, anyhow, bail};
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Error, Formatter};
use std::rc::{Rc, Weak};

static VALID_BF_CHARS: &str = "+-<>[],.";

#[derive(Debug)]
enum Item {
    MoveTo(isize),
    Verbatim(String),
    Indent(usize),
    NewLine,
}

struct Indent();

#[derive(Debug)]
struct Emitter {
    items: Vec<Item>,
    indents: Vec<Weak<Indent>>,
}

impl Emitter {
    pub fn new() -> Self {
        Self {
            items: Vec::new(),
            indents: Vec::new(),
        }
    }

    fn update_indent(&mut self) {
        self.indents.retain(|x| x.strong_count() > 0);
        self.items.push(Item::Indent(self.indents.len()));
    }

    pub fn move_to<T: VariableLike>(&mut self, x: &T) {
        self.update_indent();
        self.items.push(Item::MoveTo(x.address()));
    }

    pub fn add_code(&mut self, code: String) -> Result<()> {
        self.update_indent();
        if code.chars().any(|c| !VALID_BF_CHARS.contains(c)) {
            return Err(anyhow!("Invalid character in code: {}", code));
        }
        self.items.push(Item::Verbatim(code));
        Ok(())
    }

    pub fn add_comment(&mut self, comment: String) -> Result<()> {
        self.update_indent();
        if comment.chars().any(|c| VALID_BF_CHARS.contains(c)) {
            return Err(anyhow!("Code character in comment: {}", comment));
        }
        self.items.push(Item::Verbatim(comment));
        Ok(())
    }

    pub fn add_indent_comment_newline(&mut self, comment: String) -> Result<Rc<Indent>> {
        let i = self.indent();
        self.add_comment(comment)?;
        self.newline();
        Ok(i)
    }

    pub fn indent(&mut self) -> Rc<Indent> {
        let indent = Rc::new(Indent());
        self.indents.push(Rc::downgrade(&indent));
        self.items.push(Item::Indent(self.indents.len()));
        indent
    }

    pub fn newline(&mut self) {
        self.items.push(Item::NewLine);
    }

    pub fn emit(&self) -> String {
        let mut indent = 0;
        static INDENTATION: &str = "  ";
        let mut address = 0;
        let mut is_on_new_line = true;
        let mut pieces = Vec::new();
        for item in &self.items {
            match item {
                Item::MoveTo(_) | Item::Verbatim(_) => {
                    if is_on_new_line {
                        is_on_new_line = false;
                        // Everything is indented by 1 at least, so we subtract 1.
                        pieces.push(INDENTATION.repeat(0.max(indent - 1)));
                    }
                    match item {
                        Item::MoveTo(new_address) => {
                            let diff = new_address - address;
                            address = *new_address;
                            if diff > 0 {
                                pieces.push(">".repeat(diff as usize));
                            } else if diff < 0 {
                                pieces.push("<".repeat(-diff as usize));
                            }
                        }
                        Item::Verbatim(code) => pieces.push(code.clone()),
                        _ => unreachable!(),
                    }
                }
                Item::Indent(i) => {
                    indent = *i;
                }
                Item::NewLine => {
                    pieces.push("\n".to_string());
                    is_on_new_line = true;
                }
            }
        }
        pieces.into_iter().collect()
    }
}

#[derive(Debug)]
struct Runtime {
    context: Rc<RefCell<Context>>,
    current_address: isize,
    emitter: Emitter,
}

macro_rules! bf {
    ($emitter:expr; $($rest:tt)*) => {let mut emitter=$emitter; bf_impl!(&mut emitter; $($rest)*); emitter.newline(); };
}

macro_rules! bf_impl {
    ($emitter:expr; mv($src:ident, $dst:ident) $($rest:tt)*) => {let mut emitter=$emitter; bf_impl!(&mut emitter; $dst[-]$src[$dst+$src-] $($rest)*);};
    ($emitter:expr; $v:ident $($rest:tt)*) => {let mut emitter=$emitter; emitter.move_to($v.as_variable_like_ref()); bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; + $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code("+".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; - $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code("-".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; . $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code(".".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; , $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code(",".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; .. $($rest:tt)*) => {let mut emitter=$emitter; bf_impl!(&mut emitter; . . $($rest)*); };
    ($emitter:expr; < $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code("<".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; << $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code("<<".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; > $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code(">".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; >> $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code(">>".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; -> $($rest:tt)*) => {let mut emitter=$emitter; emitter.add_code("->".into())?; bf_impl!(&mut emitter; $($rest)*); };
    ($emitter:expr; [ $($body:tt)* ] $($rest:tt)* ) => {
        let mut emitter=$emitter; emitter.add_code("[".into())?; bf_impl!(&mut emitter; $($body)*); emitter.add_code("]".into())?; bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; ) => { };
}

impl Runtime {
    pub fn new() -> Self {
        Self {
            context: Context::new(),
            current_address: 0,
            emitter: Emitter::new(),
        }
    }

    fn copy<
        T1: VariableLike + for<'a> AsVariableLikeRef<'a>,
        T2: VariableLike + for<'b> AsVariableLikeRef<'b>,
    >(
        &mut self,
        from: &T1,
        to: &T2,
    ) -> Result<()> {
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("copy({:?}; {:?})", from, to))?;
        let t_rc = self.context.add_temp()?;
        let t = t_rc.as_ref();
        bf!(&mut self.emitter;
            t[-] to[-]
            from[to+t+from-]
            t[from+t-]
        );
        Ok(())
    }

    fn wrap_temp(&mut self, var: Rc<Variable>) -> Result<Rc<Variable>> {
        if var.is_temp() {
            return Ok(var);
        }
        let t = self.context.add_temp()?;
        self.copy(&*var, &*t)?;
        Ok(t)
    }

    fn compile_expression(&mut self, expr: &ast::Expression) -> Result<Rc<Variable>> {
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("{:?}", expr))?;
        match expr {
            ast::Expression::Literal(l) => {
                let result = self.context.add_temp()?;
                self.emitter
                    .add_comment(format!("creating literal {} into {:?}", l, result))?;
                self.emitter.move_to(&*result);
                self.emitter.add_code("[-]".into())?;
                self.emitter.add_code("+".repeat(*l as usize))?;
                self.emitter.newline();
                Ok(result)
            }
            ast::Expression::Not(expr) => {
                let x = self.compile_expression(expr)?;
                let t = self.context.add_temp()?;
                bf!(&mut self.emitter;
                    t[-]+
                    x[-t-x]t[x+t-]
                );
                Ok(x)
            }
            ast::Expression::Binary(x, opcode, y) => match opcode {
                &ast::Opcode::Mul => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let t0 = self.context.add_temp()?;
                    let t1 = self.context.add_temp()?;
                    bf!(&mut self.emitter;
                        t0[-]
                        t1[-]
                        x[t1+x-]
                        t1[
                            y[x+t0+y-]t0[y+t0-]
                        t1-]
                    );
                    Ok(x)
                }
                &ast::Opcode::Div => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let t0 = self.context.add_temp()?;
                    let t1 = self.context.add_temp()?;
                    let t2 = self.context.add_temp()?;
                    let t3 = self.context.add_temp()?;
                    bf!(&mut self.emitter;
                            t0[-] t1[-] t2[-] t3[-]
                            x[t0+x-]
                                t0[
                                    y[t1+t2+y-]
                                    t2[y+t2-]
                                    t1[
                                    t2+
                                    t0-[t2[-]t3+t0-]
                                    t3[t0+t3-]
                                    t2[
                                        t1-
                                        [x-t1[-]]+
                                    t2-]
                                t1-]
                                x+
                            t0]);
                    Ok(x)
                }
                &ast::Opcode::Mod => unimplemented!("Mod operator not implemented"),
                &ast::Opcode::Add => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    bf!(&mut self.emitter; y[-x+y] );
                    Ok(x)
                }
                &ast::Opcode::Sub => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    bf!(&mut self.emitter; y[-x-y] );
                    Ok(x)
                }
                &ast::Opcode::And => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    let z = self.context.add_temp()?;
                    bf!(&mut self.emitter;
                        z[-]
                        x[
                            y[z+y-]
                            x-
                        ]
                    );
                    Ok(z)
                }
                &ast::Opcode::Or => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    let z = self.context.add_temp()?;
                    bf!(&mut self.emitter;
                        z[-]
                        x[y+x-]
                        y[[-]z+y]
                    );
                    Ok(z)
                }
                &ast::Opcode::Lt => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let temp0 = self.context.add_temp()?;
                    let temp1 = self.context.add_temp_with_size(3)?;
                    bf!(&mut self.emitter;
                        temp0[-]
                        temp1[-] >[-]+ >[-] <<
                        y[temp0+ temp1+ y-]
                        temp0[y+ temp0-]
                        x[temp0+ x-]+
                        temp1[>-]> [< x- temp0[-] temp1>->]<+<
                        temp0[temp1- [>-]> [< x- temp0[-]+ temp1>->]<+< temp0-]
                    );
                    Ok(x)
                }
                &ast::Opcode::Le => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let temp0 = self.context.add_temp()?;
                    let temp1 = self.context.add_temp_with_size(3)?;
                    bf!(&mut self.emitter;
                        temp0[-]
                        temp1[-] >[-]+ >[-] <<
                        y[temp0+ temp1+ y-]
                        temp1[y+ temp1-]
                        x[temp1+ x-]
                        temp1[>-]> [< x+ temp0[-] temp1>->]<+<
                        temp0[temp1- [>-]> [< x+ temp0[-]+ temp1>->]<+< temp0-]
                    );
                    Ok(x)
                }
                &ast::Opcode::Eq => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    bf!(&mut self.emitter;
                        x[-y-x]+y[x-y[-]]
                    );
                    Ok(x)
                }
                &ast::Opcode::Ne => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    bf!(&mut self.emitter;
                        x[
                            y-x-]
                        y[[-]
                            x+y]
                    );
                    Ok(x)
                }
            },
            ast::Expression::Variable(name) => {
                let v = self
                    .context
                    .borrow()
                    .get_variable(name)
                    .ok_or_else(|| anyhow!("Variable {} not found in context", name))?;
                Ok(v)
            }
            ast::Expression::ArrayLookup(name, index) => {
                let array = self
                    .context
                    .borrow()
                    .get_variable(name)
                    .ok_or_else(|| anyhow!("Variable {} not found in context", name))?;
                let result = self.context.add_temp()?;
                let index = self.compile_expression(index)?;
                let before_head = array.predecessor();
                let space = array.successor(0);
                let index1 = array.successor(1);
                let index2 = array.successor(2);
                let data = array.successor(3);
                let after_head = array.successor(4);
                self.copy(&*index, &index1)?;
                self.copy(&*index, &index2)?;
                {
                    let _indent = self
                        .emitter
                        .add_indent_comment_newline("move head to array index".into())?;
                    bf!(&mut self.emitter;
                        index1[-
                            mv(after_head, space)
                            mv(index2, data)
                            mv(index1, index2)
                            >
                            index1
                        ]
                    );
                }
                self.copy(&after_head, &data)?;
                {
                    let _indent = self
                        .emitter
                        .add_indent_comment_newline("move head back".into())?;
                    bf!(&mut self.emitter;
                        index2[-
                            mv(index2, index1)
                            mv(data, index2)
                            mv(before_head, data)
                            <
                            index2
                        ]
                    );
                }
                self.copy(&data, &result)?;
                Ok(result)
            }
            ast::Expression::Assignment(name, expr) => {
                let x = self.compile_expression(expr)?;
                let v = self
                    .context
                    .borrow()
                    .get_variable(name)
                    .ok_or_else(|| anyhow!("Variable {} not found in context", name))?;
                self.copy(&x, &v)?;
                Ok(x)
            }
            ast::Expression::ArrayAssignment(name, index, expr) => {
                let array = self
                    .context
                    .borrow()
                    .get_variable(name)
                    .ok_or_else(|| anyhow!("Variable {} not found in context", name))?;
                let result = self.context.add_temp()?;
                let index = self.compile_expression(index)?;
                let value = self.compile_expression(expr)?;
                let before_head = array.predecessor();
                let space = array.successor(0);
                let index1 = array.successor(1);
                let index2 = array.successor(2);
                let data = array.successor(3);
                self.copy(&value, &data)?;
                let after_head = array.successor(4);
                self.copy(&index, &index1)?;
                self.copy(&index, &index2)?;
                {
                    let _indent = self
                        .emitter
                        .add_indent_comment_newline("move head to array index".into())?;
                    bf!(&mut self.emitter;
                        index1[-
                            mv(after_head, space)
                            mv(data, after_head)
                            mv(index2, data)
                            mv(index1, index2)
                            >
                            index1
                        ]
                    );
                }
                self.copy(&data, &after_head)?;
                {
                    let _indent = self
                        .emitter
                        .add_indent_comment_newline("move head back".into())?;
                    bf!(&mut self.emitter;
                        index2[-
                            mv(index2, index1)
                            mv(before_head, data)
                            <
                            index2
                        ]
                    );
                }
                self.copy(&data, &result)?;
                Ok(value)
            }
        }
    }

    pub fn compile(&mut self, statement: &ast::Statement) -> Result<()> {
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("{:?}", statement))?;
        match statement {
            ast::Statement::VarDeclaration(name, init) => {
                let v = self.context.add(name)?;
                let init = self.compile_expression(init)?;
                self.copy(&init, &v)?;
            }
            ast::Statement::ArrayDeclaration(name, init) => {
                let array_head_size = 4;
                let a = self
                    .context
                    .add_with_size(name, init.len() + array_head_size)?;
                for (i, expr) in init.iter().enumerate() {
                    let value = self.compile_expression(expr)?;
                    let index = a.successor(i + array_head_size);
                    self.copy(&value, &index)?;
                }
            }
            ast::Statement::If(cond, then, else_) => {
                let cond = self.compile_expression(cond)?;
                let t0 = self.context.add_temp()?;
                let t1 = self.context.add_temp()?;
                bf!(&mut self.emitter;
                    t0[-]+
                    t1[-]
                    cond
                );
                self.emitter.add_code("[".into())?;
                self.compile(then)?;
                bf!(&mut self.emitter;
                    t0-
                    cond[t1+cond-]
                );
                self.emitter.add_code("]".into())?;
                // else branch
                if let Some(else_) = else_ {
                    bf!(&mut self.emitter;
                        t1[cond+t1-]
                        t0
                    );
                    self.emitter.add_code("[".into())?;
                    self.compile(else_)?;
                    bf!(&mut self.emitter;
                        t0-
                    );
                    self.emitter.add_code("]".into())?;
                }
            }
            ast::Statement::PutChar(expr) => {
                let e = self.compile_expression(expr)?;
                self.emitter.move_to(&e);
                self.emitter.add_code(".".into())?;
            }
            ast::Statement::While(cond, body) => {
                // We do some extra hoops here, to only add the condition code once.
                // See: https://esolangs.org/wiki/Brainfuck_algorithms#while_(x)_{_code_}
                let zero = self.context.add_temp()?;
                self.emitter.move_to(&zero);
                self.emitter.add_code("[-]".into())?;
                let t = self.context.add_temp()?;
                self.emitter.move_to(&t);
                self.emitter.add_code("[-]+[".into())?;
                self.emitter.move_to(&t);
                self.emitter.add_code("-".into())?;
                let c = self.compile_expression(cond)?;
                self.emitter.move_to(&c);
                self.emitter.add_code("[".into())?;
                self.compile(&body)?;
                self.emitter.move_to(&t);
                self.emitter.add_code("+".into())?;
                self.emitter.move_to(&zero);
                self.emitter.add_code("]".into())?;
                self.emitter.move_to(&t);
                self.emitter.add_code("]".into())?;
            }
            ast::Statement::Block(statements) => {
                self.context.borrow_mut().push_scope();
                for statement in statements {
                    self.compile(statement)?;
                }
                self.context.borrow_mut().pop_scope()?;
            }
            ast::Statement::Expression(expr) => {
                self.compile_expression(expr)?;
            }
        }
        Ok(())
    }
}

pub fn compile_bf_script(program: &str) -> Result<String> {
    let ops = ProgramParser::new()
        .parse(program)
        .map_err(|e| anyhow!("{}", e))?;
    let mut runtime = Runtime::new();
    for op in ops {
        runtime.compile(&op)?;
    }
    Ok(runtime.emitter.emit())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfi::run_program_from_str;

    #[test]
    fn test_putc_literal() {
        let mut runtime = Runtime::new();
        let expr = ast::Expression::Literal(3);
        runtime.compile(&ast::Statement::PutChar(expr)).unwrap();
        assert_eq!(
            runtime.emitter.emit(),
            "putc(3);\n  3\n  creating literal 3 into __temp0{0}[-]+++\n."
        );
    }

    #[test]
    fn test_putc_not_2() {
        let mut runtime = Runtime::new();
        let expr = ast::Expression::Not(Box::new(ast::Expression::Literal(2)));
        runtime.compile(&&ast::Statement::PutChar(expr)).unwrap();
        assert_eq!(
            runtime.emitter.emit(),
            "putc(!2);\n  !2\n    2\n    creating literal 2 into __temp0{0}[-]++\n  >[-]+<[->-<]>[<+>-]\n<."
        );
    }

    #[test]
    fn test_end2end_literal() {
        let bf_code = compile_bf_script(r#"putc("3");"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "3");
    }

    #[test]
    fn test_end2end_add_sub() {
        let bf_code = compile_bf_script(r#"putc("0" + 99 - 90);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "9");
    }

    #[test]
    fn test_end2end_mul() {
        let bf_code = compile_bf_script(r#"putc("0" + 2 * 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "6");
    }

    #[test]
    fn test_end2end_div() {
        let bf_code = compile_bf_script(r#"putc("0" + 15 / 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "5");
    }

    #[test]
    fn test_end2end_and() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (1 && 0));putc("0" + (1 && 7) / (1 && 7));"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "01");
    }

    #[test]
    fn test_end2end_or() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 || 0));putc("0" + (0 || 6) / (0 || 6));"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "01");
    }

    #[test]
    fn test_end2end_lt() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 < 17));putc("0" + (3 < 2));putc("0" + (3 < 3));"#)
                .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "100");
    }

    #[test]
    fn test_end2end_le() {
        let bf_code = compile_bf_script(
            r#"putc("0" + (0 <= 17));putc("0" + (3 <= 2));putc("0" + (3 <= 3));"#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "101");
    }

    #[test]
    fn test_end2end_eq() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 == 0));putc("0" + (3 == 3));putc("0" + (3 == 2));"#)
                .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "110");
    }

    #[test]
    fn test_end2end_ne() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 != 0));putc("0" + (3 != 3));putc("0" + (3 != 2));"#)
                .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "001");
    }

    #[test]
    fn test_end2end_var() {
        let bf_code =
            compile_bf_script(r#"var x = "0"; putc(x + 2); x = x+1; putc(x + 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "24");
    }

    #[test]
    fn test_end2end_array_simple() {
        let bf_code = compile_bf_script(r#"var s[] = [7]; putc("0" + s[0]);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(100_000)).unwrap();
        assert_eq!(output, "7");
    }

    #[test]
    fn test_end2end_array() {
        let bf_code =
            compile_bf_script(r#"
            var s[] = "Hello "; putc(s[0]); putc(s[1]); putc(s[2]); putc(s[3]); putc(s[4]); putc(s[5]);
            s[0] = "W"; s[1] = "o"; s[2] = "r"; s[3] = "l"; s[4] = "d";
            putc(s[0]); putc(s[1]); putc(s[2]); putc(s[3]); putc(s[4]);
        "#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(1_000_000)).unwrap();
        assert_eq!(output, "Hello World");
    }

    #[test]
    fn test_block_scope_simple() {
        compile_bf_script(
            r#"
            var x = 1; { x = 2; }
        "#,
        )
        .unwrap();
    }

    #[test]
    fn test_block_var_not_in_scope() {
        let bf_code = compile_bf_script(
            r#"
            {var x = 1;} x = 2;
        "#,
        );
        assert_eq!(
            bf_code.err().unwrap().to_string(),
            "Variable x not found in context"
        );
    }

    #[test]
    fn test_end2end_while() {
        let bf_code = compile_bf_script(
            r#"
                var x = 9;
                while x {
                    putc("0" + x);
                    x = x - 1;
                }
            "#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "987654321");
    }

    #[test]
    fn test_end2end_if_else() {
        let bf_code = compile_bf_script(
            r#"
                if 2 == 1 + 1 then {
                    putc("A");
                }
                if 2 == 1 then {
                    putc("B");
                }
                if 2 == 1 + 1 then {
                    putc("C");
                } else {
                    putc("D");
                }
                if 2 == 1 then {
                    putc("F");
                } else {
                    putc("G");
                }
            "#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "ACG");
    }
}
