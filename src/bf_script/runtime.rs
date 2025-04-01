use super::{ast, parser::ProgramParser};
use anyhow::{Result, anyhow, bail};
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

#[derive(Debug)]
pub struct Variable {
    name: String,
    is_temp: bool,
    address: isize,
    size: usize,
    // Store a weak reference to avoid a reference cycle.
    context: Weak<RefCell<Context>>,
}

impl Drop for Variable {
    fn drop(&mut self) {
        // Attempt to upgrade the weak reference.
        if let Some(ctx) = self.context.upgrade() {
            // Deregister self from the context.
            ctx.borrow_mut()
                .deregister(&self.name, self.address, self.size)
                .unwrap();
        }
    }
}

impl Variable {
    pub fn predecessor(&self) -> Variable {
        Variable {
            name: format!("predecessor({})", self.name),
            is_temp: self.is_temp,
            address: self.address - 1,
            size: 1,
            context: self.context.clone(),
        }
    }
    pub fn successor(&self, pos: usize) -> Variable {
        Variable {
            name: format!("successor({}, {})", self.name, pos),
            is_temp: self.is_temp,
            address: self.address + pos as isize,
            size: 1,
            context: self.context.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Context {
    variables: HashMap<String, Weak<Variable>>,
    used_addresses: HashSet<isize>,
    temp_count: usize,
}

impl Context {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            variables: HashMap::new(),
            used_addresses: HashSet::new(),
            temp_count: 0,
        }))
    }

    fn get_variable(&self, name: &str) -> Option<Rc<Variable>> {
        self.variables
            .get(name)
            .and_then(|weak_var| weak_var.upgrade())
    }

    fn deregister(&mut self, name: &str, address: isize, size: usize) -> Result<()> {
        for i in 0..size {
            self.used_addresses.remove(&(address + i as isize));
        }
        self.variables.remove(name);
        Ok(())
    }

    fn add_impl(
        context: &Rc<RefCell<Self>>,
        name: &str,
        is_temp: bool,
        size: usize,
    ) -> Result<Rc<Variable>> {
        let weak_ctx = Rc::downgrade(context);
        let mut ctx = context.borrow_mut();
        let address = ctx.find_next_free(size);
        match ctx.variables.entry(name.to_string()) {
            Entry::Occupied(_) => Err(anyhow!("Variable {} already exists", name)),
            Entry::Vacant(entry) => {
                let variable = Rc::new(Variable {
                    name: name.to_string(),
                    is_temp,
                    address,
                    size,
                    context: weak_ctx,
                });
                entry.insert(Rc::downgrade(&variable));
                for i in 0..size {
                    ctx.used_addresses.insert(variable.address + i as isize);
                }
                Ok(variable)
            }
        }
    }

    fn add_temp_impl(context: &Rc<RefCell<Self>>, size: usize) -> Result<Rc<Variable>> {
        let name;
        {
            let temp_count = &mut context.borrow_mut().temp_count;
            name = format!("__temp{}", temp_count);
            *temp_count += 1;
        }
        Self::add_impl(context, &name, true, size)
    }

    fn find_next_free(&self, size: usize) -> isize {
        let top_address = self.used_addresses.iter().max().map_or(0, |&x| x + 1);
        let mut address = 0;
        while address < top_address {
            let mut is_free = true;
            for i in 0..size {
                if self.used_addresses.contains(&(address + i as isize)) {
                    is_free = false;
                    address += 1 + i as isize;
                    break;
                }
            }
            if is_free {
                return address;
            }
        }
        top_address
    }
}

pub trait ContextExt {
    fn add_with_size(&self, name: &str, size: usize) -> Result<Rc<Variable>>;
    fn add(&self, name: &str) -> Result<Rc<Variable>>;
    fn add_temp(&self) -> Result<Rc<Variable>>;
    fn add_temp_with_size(&self, size: usize) -> Result<Rc<Variable>>;
}

impl ContextExt for Rc<RefCell<Context>> {
    fn add_with_size(&self, name: &str, size: usize) -> Result<Rc<Variable>> {
        Context::add_impl(self, name, false, size)
    }
    fn add(&self, name: &str) -> Result<Rc<Variable>> {
        Context::add_impl(self, name, false, 1)
    }
    fn add_temp(&self) -> Result<Rc<Variable>> {
        Context::add_temp_impl(self, 1)
    }
    fn add_temp_with_size(&self, size: usize) -> Result<Rc<Variable>> {
        Context::add_temp_impl(self, size)
    }
}

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

    pub fn move_to(&mut self, address: &Variable) {
        self.update_indent();
        self.items.push(Item::MoveTo(address.address));
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
    ($emitter:expr; $v:ident $($rest:tt)*) => {let mut emitter=$emitter; emitter.move_to(&$v); bf_impl!(&mut emitter; $($rest)*); };
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

    fn copy(&mut self, from: &Variable, to: &Variable) -> Result<()> {
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("Copy {:?}->{:?}", from, to))?;
        let t = self.context.add_temp()?;
        bf!(&mut self.emitter;
            t[-] to[-]
            from[to+t+from-]
            t[from+t-]
        );
        Ok(())
    }

    fn wrap_temp(&mut self, var: Rc<Variable>) -> Result<Rc<Variable>> {
        if var.is_temp {
            return Ok(var);
        }
        let t = self.context.add_temp()?;
        self.copy(&var, &t)?;
        Ok(t)
    }

    fn compile_expression(&mut self, expr: &ast::Expression) -> Result<Rc<Variable>> {
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("{:?}", expr))?;
        match expr {
            ast::Expression::Literal(l) => {
                let result = self.context.add_temp()?;
                self.emitter.move_to(&result);
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
                self.copy(&index, &index1)?;
                self.copy(&index, &index2)?;
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
                bail!("VarDeclaration statement not implemented");
            }
            ast::Statement::ArrayDeclaration(name, init) => {
                bail!("ArrayDeclaration statement not implemented");
            }
            ast::Statement::If(cond, then, else_) => {
                bail!("If statement not implemented");
            }
            ast::Statement::PutChar(expr) => {
                let e = self.compile_expression(expr)?;
                self.emitter.move_to(&e);
                self.emitter.add_code(".".into())?;
            }
            ast::Statement::While(cond, body) => {
                bail!("While statement not implemented");
            }
            ast::Statement::Block(statements) => {
                bail!("Block statement not implemented");
            }
            ast::Statement::Expression(expr) => {
                bail!("Expression statement not implemented");
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
    fn test_add() {
        let ctx = Context::new();
        let var1 = ctx.add_with_size("var1", 4).unwrap();
        let var2 = ctx.add_with_size("var2", 2).unwrap();

        assert_eq!(var1.name, "var1");
        assert_eq!(var1.size, 4);
        assert_eq!(var1.address, 0);

        assert_eq!(var2.name, "var2");
        assert_eq!(var2.size, 2);
        assert_eq!(var2.address, 4);
    }

    #[test]
    fn test_add_collision() {
        let ctx = Context::new();
        let _var1 = ctx.add_with_size("foo", 4).unwrap();
        assert!(ctx.add_with_size("foo", 2).is_err());
    }

    #[test]
    fn test_add_after_drop() {
        let ctx = Context::new();
        let _v1 = ctx.add_with_size("var1", 4);
        {
            let _v2 = ctx.add_temp();
            assert_eq!(ctx.add_temp().unwrap().address, 5); // Address after var2
        }
        // var2 goes out of scope
        assert_eq!(ctx.add_temp().unwrap().address, 4); // Address after var1
    }

    #[test]
    fn test_putc_literal() {
        let mut runtime = Runtime::new();
        let expr = ast::Expression::Literal(3);
        runtime.compile(&ast::Statement::PutChar(expr)).unwrap();
        assert_eq!(runtime.emitter.emit(), "putc(3);\n  3\n  [-]+++\n.");
    }

    #[test]
    fn test_putc_not_2() {
        let mut runtime = Runtime::new();
        let expr = ast::Expression::Not(Box::new(ast::Expression::Literal(2)));
        runtime.compile(&&ast::Statement::PutChar(expr)).unwrap();
        assert_eq!(
            runtime.emitter.emit(),
            "putc(!2);\n  !2\n    2\n    [-]++\n  >[-]+<[->-<]>[<+>-]\n<."
        );
    }

    #[test]
    fn test_end2end_literal() {
        let bf_code = compile_bf_script(r#"putc("3");"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "3");
    }

    #[test]
    fn test_end2end_add_sub() {
        let bf_code = compile_bf_script(r#"putc("0" + 99 - 90);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "9");
    }

    #[test]
    fn test_end2end_mul() {
        let bf_code = compile_bf_script(r#"putc("0" + 2 * 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "6");
    }

    #[test]
    fn test_end2end_div() {
        let bf_code = compile_bf_script(r#"putc("0" + 15 / 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "5");
    }

    #[test]
    fn test_end2end_and() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (1 && 0));putc("0" + (1 && 7) / (1 && 7));"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "01");
    }

    #[test]
    fn test_end2end_or() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 || 0));putc("0" + (0 || 6) / (0 || 6));"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "01");
    }

    #[test]
    fn test_end2end_lt() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 < 17));putc("0" + (3 < 2));putc("0" + (3 < 3));"#)
                .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "100");
    }

    #[test]
    fn test_end2end_le() {
        let bf_code = compile_bf_script(
            r#"putc("0" + (0 <= 17));putc("0" + (3 <= 2));putc("0" + (3 <= 3));"#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "101");
    }

    #[test]
    fn test_end2end_eq() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 == 0));putc("0" + (3 == 3));putc("0" + (3 == 2));"#)
                .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "110");
    }

    #[test]
    fn test_end2end_ne() {
        let bf_code =
            compile_bf_script(r#"putc("0" + (0 != 0));putc("0" + (3 != 3));putc("0" + (3 != 2));"#)
                .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_0000)).unwrap();
        assert_eq!(output, "001");
    }
}
