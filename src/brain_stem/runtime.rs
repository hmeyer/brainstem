#![deny(unused_must_use)]
use super::{
    ast, context::AsVariableLikeRef, context::Context, context::ContextExt,
    context::StackFrameOffset, context::Successor, context::Variable, context::VariableExt,
    context::VariableLike, parser::ProgramParser,
};
use anyhow::{Result, anyhow};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::{Rc, Weak};

static VALID_BF_CHARS: &str = "+-<>[],.";
static LINMEM: &str = "__LINMEM__";
static STACKDEPTH: &str = "__STACKDEPTH__";

#[derive(Debug, Clone)]
enum Item {
    MoveTo(isize),
    MoveToInStackFrameAbove(isize),
    MoveToInStackFrameBelow(isize),
    StackFrameUp,
    StackFrameDown,
    AddStackFrameSize,
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

    pub fn move_to<T: VariableLike>(&mut self, x: &T) -> Result<()> {
        self.update_indent();
        self.add_comment(format!("{:?}", x))?;
        match x.stackframe() {
            Some(StackFrameOffset::Above) => {
                self.items.push(Item::MoveToInStackFrameAbove(x.address()))
            }
            Some(StackFrameOffset::Below) => {
                self.items.push(Item::MoveToInStackFrameBelow(x.address()))
            }
            None => self.items.push(Item::MoveTo(x.address())),
        }
        Ok(())
    }

    pub fn stackframe_up(&mut self) {
        self.update_indent();
        self.items.push(Item::StackFrameUp);
    }

    pub fn stackframe_down(&mut self) {
        self.update_indent();
        self.items.push(Item::StackFrameDown);
    }

    pub fn add_stackframe_size(&mut self) {
        self.update_indent();
        self.items.push(Item::AddStackFrameSize);
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

    pub fn emit(&self, stackframe_size: usize) -> String {
        let mut indent = 0;
        static INDENTATION: &str = "  ";
        let mut address = 0;
        let mut is_on_new_line = true;
        let mut pieces = Vec::new();
        let resolved_items = self.items.iter().map(|item| match item {
            Item::MoveToInStackFrameAbove(addr) => Item::MoveTo(addr + stackframe_size as isize),
            Item::MoveToInStackFrameBelow(addr) => Item::MoveTo(addr - stackframe_size as isize),
            Item::StackFrameUp => Item::Verbatim(">".repeat(stackframe_size)),
            Item::StackFrameDown => Item::Verbatim("<".repeat(stackframe_size)),
            Item::AddStackFrameSize => Item::Verbatim("+".repeat(stackframe_size)),
            _ => item.clone(),
        });
        for item in resolved_items {
            match item {
                Item::MoveToInStackFrameAbove(_) => unreachable!(),
                Item::MoveToInStackFrameBelow(_) => unreachable!(),
                Item::StackFrameUp => unreachable!(),
                Item::StackFrameDown => unreachable!(),
                Item::AddStackFrameSize => unreachable!(),
                Item::MoveTo(_) | Item::Verbatim(_) => {
                    if is_on_new_line {
                        is_on_new_line = false;
                        // Everything is indented by 1 at least, so we subtract 1.
                        pieces.push(INDENTATION.repeat(0.max(indent - 1)));
                    }
                    match item {
                        Item::MoveTo(new_address) => {
                            let diff = new_address - address;
                            address = new_address;
                            match diff.cmp(&0) {
                                std::cmp::Ordering::Equal => {}
                                std::cmp::Ordering::Greater => {
                                    pieces.push(">".repeat(diff as usize));
                                }
                                std::cmp::Ordering::Less => {
                                    pieces.push("<".repeat(-diff as usize));
                                }
                            }
                        }
                        Item::Verbatim(code) => pieces.push(code.clone()),
                        _ => unreachable!(),
                    }
                }
                Item::Indent(i) => {
                    indent = i;
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
    emitter: Emitter,
    max_stackframe_size: usize,
}

macro_rules! bf {
    ($emitter:expr; $($rest:tt)*) => {
            let mut emitter=$emitter;
            bf_impl!(&mut emitter; $($rest)*);
    };
}

macro_rules! bf_impl {
    ($emitter:expr; mv($src:ident, $dst:ident) $($rest:tt)*) => {
        let mut emitter=$emitter;
        bf_impl!(&mut emitter; $dst[-]$src[$dst+$src-] $($rest)*);
    };
    ($emitter:expr; $v:ident $($rest:tt)*) => {
        #[allow(unused_mut)]
        {
            let mut emitter=$emitter;
            emitter.move_to($v.as_variable_like_ref())?;
            bf_impl!(&mut emitter; $($rest)*);
        }
    };
    ($emitter:expr; + $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code("+".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; - $($rest:tt)*) => {
        #[allow(unused_mut)]
        let mut emitter=$emitter;
        emitter.add_code("-".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; . $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code(".".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; , $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code(",".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; .. $($rest:tt)*) => {
        let mut emitter=$emitter;
        bf_impl!(&mut emitter; . . $($rest)*);
    };
    ($emitter:expr; < $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code("<".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; << $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code("<<".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; > $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code(">".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; >> $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code(">>".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; -> $($rest:tt)*) => {
        let mut emitter=$emitter;
        emitter.add_code("->".into())?;
        bf_impl!(&mut emitter; $($rest)*);
    };
    ($emitter:expr; [ $($body:tt)* ] $($rest:tt)* ) => {
        #[allow(unused_mut)]
        {
            let mut emitter=$emitter;
            emitter.add_code("[".into())?;
            bf_impl!(&mut emitter; $($body)*);
            emitter.add_code("]".into())?;
            bf_impl!(&mut emitter; $($rest)*);
        }
    };
    ($emitter:expr; ) => { };
}

impl Runtime {
    pub fn new() -> Self {
        let ctx = Context::new();
        ctx.add_with_size(LINMEM, 4).unwrap();
        ctx.add(STACKDEPTH).unwrap();
        Self {
            context: ctx,
            emitter: Emitter::new(),
            max_stackframe_size: 0,
        }
    }

    fn get_max_stackframe_size(&self) -> usize {
        self.max_stackframe_size
    }

    fn copy_using_temp<
        T1: VariableLike + for<'a> AsVariableLikeRef<'a>,
        T2: VariableLike + for<'b> AsVariableLikeRef<'b>,
    >(
        &mut self,
        from: &T1,
        to: &T2,
        temp: &Variable,
    ) -> Result<()> {
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("copy({:?}; {:?}; using {:?})", from, to, temp))?;
        bf!(&mut self.emitter;
            temp[-] to[-]
            from[to+temp+from-]
            temp[from+temp-]
        );
        self.emitter.newline();
        Ok(())
    }

    fn copy<
        T1: VariableLike + for<'a> AsVariableLikeRef<'a>,
        T2: VariableLike + for<'b> AsVariableLikeRef<'b>,
    >(
        &mut self,
        from: &T1,
        to: &T2,
    ) -> Result<()> {
        let t_rc = self.context.add_temp()?;
        self.copy_using_temp(from, to, &t_rc)
    }

    fn wrap_temp(&mut self, var: Rc<Variable>) -> Result<Rc<Variable>> {
        if var.is_temp() {
            return Ok(var);
        }
        let t = self.context.add_temp()?;
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("wrap_temp({:?})", var))?;
        self.copy(&*var, &*t)?;
        Ok(t)
    }

    fn mem_lookup(
        &mut self,
        mem_control_block: Successor,
        index: &ast::Expression,
    ) -> Result<Rc<Variable>> {
        let result = self.context.add_temp()?;
        // We shift the memory control block by one, b/c for reading we only need three elements.
        let mem_control_block = mem_control_block.successor(1);
        let memory_after = mem_control_block.successor(-1);
        let data = mem_control_block.successor(0);
        let index2 = mem_control_block.successor(1);
        let index1 = mem_control_block.successor(2);
        let memory_before = mem_control_block.successor(3);

        // We use this structure to move into the memory:
        // --> moving direction --> memory_after | data | index2 | index1 | memory_before
        {
            let index = self.compile_expression(index)?;
            self.copy(&*index, &index1)?;
            self.copy(&*index, &index2)?;
        }
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head to array index".into())?;
            bf!(&mut self.emitter;
                index1[-
                    mv(memory_before, data)
                    mv(index1, memory_before)
                    mv(index2, index1)
                    index1
                    >
                ]
            );
        }
        {
            let _indent = self.emitter.add_indent_comment_newline(format!(
                "copy {:?} to {:?} using {:?} (already zero) as temp",
                memory_before, data, index1
            ))?;
            bf!(&mut self.emitter;
                data[-]
                memory_before[data+index1+memory_before-]
                index1[memory_before+index1-]
            );
        }
        // Now we move back:
        //  <-- moving direction <-- more MEMORY | memory_after | data | index2 | index1 | memory_before | MEMORY
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head back".into())?;
            bf!(&mut self.emitter;
                index2[-
                    mv(memory_after, index1)
                    mv(data, memory_after)
                    mv(index2, data)
                    index2
                    <
                ]
            );
        }
        self.copy(&data, &result)?;
        Ok(result)
    }

    fn mem_write(
        &mut self,
        mem_control_block: Successor,
        index: &ast::Expression,
        value: &ast::Expression,
    ) -> Result<Rc<Variable>> {
        let memory_after = mem_control_block.successor(-1);
        let space = mem_control_block.successor(0);
        let data = mem_control_block.successor(1);
        let index2 = mem_control_block.successor(2);
        let index1 = mem_control_block.successor(3);
        let memory_before = mem_control_block.successor(4);

        let value = self.compile_expression(value)?;
        // We use this structure to move into the memory:
        //  --> moving direction --> memory_after | space | data | index2 | index1 | memory_before | MEMORY
        self.copy(&value, &data)?;
        {
            let index = self.compile_expression(index)?;
            self.copy(&index, &index1)?;
            self.copy(&index, &index2)?;
        }
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head to array index".into())?;
            bf!(&mut self.emitter;
                index1[-
                    mv(memory_before, space)
                    mv(index1, memory_before)
                    mv(index2, index1)
                    mv(data, index2)
                    index1
                    >
                ]
            );
        }
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline(format!("move {:?} to {:?}", data, memory_before))?;
            bf!(&mut self.emitter; mv(data, memory_before));
        }
        // Now we move back:
        //  -> moving direction -> more MEMORY | memory_after | space | data | index2 | index1 | memory_before | MEMORY
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head back".into())?;
            bf!(&mut self.emitter;
                index2[-
                    mv(memory_after, index1)
                    mv(index2, data)
                    index2
                    <
                ]
            );
        }
        Ok(value)
    }

    fn mem_lookup_backwards(
        &mut self,
        mem_control_block: Successor,
        index: &ast::Expression,
    ) -> Result<Rc<Variable>> {
        let result = self.context.add_temp()?;

        let memory_before = mem_control_block.successor(-1);
        let index1 = mem_control_block.successor(0);
        let index2 = mem_control_block.successor(1);
        let data = mem_control_block.successor(2);
        let memory_after = mem_control_block.successor(3);

        // We use this structure to move from the tail into the memory:
        // MEMORY <- moving direction <- memory_before | index1 | index2 | data | memory_after
        {
            let index = self.compile_expression(index)?;
            self.copy(&*index, &index1)?;
            self.copy(&*index, &index2)?;
        }
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head to array index".into())?;
            bf!(&mut self.emitter;
                index1[-
                    mv(memory_before, data)
                    mv(index1, memory_before)
                    mv(index2, index1)
                    index1
                    <
                ]
            );
        }
        {
            let _indent = self.emitter.add_indent_comment_newline(format!(
                "copy {:?} to {:?} using {:?} (already zero) as temp",
                memory_before, data, index1
            ))?;
            bf!(&mut self.emitter;
                data[-]
                memory_before[data+index1+memory_before-]
                index1[memory_before+index1-]
            );
        }
        // Now we move back:
        // MEMORY -> moving direction -> memory_before | index1 | index2 | data | memory_after | more MEMORY
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head back".into())?;
            bf!(&mut self.emitter;
                index2[-
                    mv(memory_after, index1)
                    mv(data, memory_after)
                    mv(index2, data)
                    index2
                    >
                ]
            );
        }
        self.copy(&data, &result)?;
        Ok(result)
    }

    fn mem_write_backwards(
        &mut self,
        mem_control_block: Successor,
        index: &ast::Expression,
        value: &ast::Expression,
    ) -> Result<Rc<Variable>> {
        let memory_before = mem_control_block.successor(-1);
        let index1 = mem_control_block.successor(0);
        let index2 = mem_control_block.successor(1);
        let data = mem_control_block.successor(2);
        let space = mem_control_block.successor(3);
        let memory_after = mem_control_block.successor(4);

        let value = self.compile_expression(value)?;
        // We use this structure to move from the tail into the memory:
        // MEMORY <- moving direction <- memory_before | index1 | index2 | data | space | memory_after
        self.copy(&value, &data)?;
        {
            let index = self.compile_expression(index)?;
            self.copy(&index, &index1)?;
            self.copy(&index, &index2)?;
        }
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head to array index".into())?;
            bf!(&mut self.emitter;
                index1[-
                    mv(memory_before, space)
                    mv(index1, memory_before)
                    mv(index2, index1)
                    mv(data, index2)
                    index1
                    <
                ]
            );
        }
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline(format!("move {:?} to {:?}", data, memory_before))?;
            bf!(&mut self.emitter; mv(data, memory_before));
        }
        // Now we move back:
        // MEMORY -> moving direction -> memory_before | index1 | index2 | data | space | memory_after | more MEMORY
        {
            let _indent = self
                .emitter
                .add_indent_comment_newline("move head back".into())?;
            bf!(&mut self.emitter;
                index2[-
                    mv(memory_after, index1)
                    mv(index2, data)
                    index2
                    >
                ]
            );
        }
        Ok(value)
    }

    fn compile_expression(&mut self, expr: &ast::Expression) -> Result<Rc<Variable>> {
        let _indent = self
            .emitter
            .add_indent_comment_newline(format!("{:?}", expr))?;
        let result = match expr {
            ast::Expression::Literal(l) => {
                let result = self.context.add_temp()?;
                self.emitter
                    .add_comment(format!("creating literal {} into {:?}", l, result))?;
                self.emitter.move_to(&*result)?;
                self.emitter.add_code("[-]".into())?;
                self.emitter.add_code("+".repeat(*l as usize))?;
                Ok(result)
            }
            ast::Expression::Not(expr) => {
                let x = self.compile_expression(expr)?;
                let x = self.wrap_temp(x)?;
                let r = self.context.add_temp()?;
                bf!(&mut self.emitter;
                    r[-]+
                    x[r-x[-]]
                );
                Ok(r)
            }
            ast::Expression::Binary(x, opcode, y) => match *opcode {
                ast::Opcode::Mul => {
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
                ast::Opcode::Div => {
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
                ast::Opcode::Mod => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let buffer = self.context.add_temp_with_size(5)?;
                    let n = buffer.successor(1);
                    let d = buffer.successor(2);
                    let r = buffer.successor(3);
                    let z0 = buffer.successor(0);
                    let z4 = buffer.successor(4);
                    let z5 = buffer.successor(5);
                    self.copy(&*x, &n)?;
                    self.copy(&*y, &d)?;
                    bf!(&mut self.emitter;
                        z0[-]z4[-]z5[-]
                        n
                        [>->+<[>]>[<+>-]<<[<]>-]
                        mv(r, x)
                        x
                    );
                    Ok(x)
                }
                ast::Opcode::Add => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    bf!(&mut self.emitter; y[-x+y] );
                    Ok(x)
                }
                ast::Opcode::Sub => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    bf!(&mut self.emitter; y[-x-y] );
                    Ok(x)
                }
                ast::Opcode::And => {
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
                ast::Opcode::Or => {
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
                ast::Opcode::Lt => {
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
                ast::Opcode::Le => {
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
                ast::Opcode::Eq => {
                    let x = self.compile_expression(x)?;
                    let x = self.wrap_temp(x)?;
                    let y = self.compile_expression(y)?;
                    let y = self.wrap_temp(y)?;
                    bf!(&mut self.emitter;
                        x[-y-x]+y[x-y[-]]
                    );
                    Ok(x)
                }
                ast::Opcode::Ne => {
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
                let v = self.context.borrow().get_variable(name)?;
                Ok(v)
            }
            ast::Expression::ArrayLookup(name, index) => {
                let array = self.context.borrow().get_variable(name)?;
                self.mem_lookup(array.successor(0), index)
            }
            ast::Expression::Assignment(name, expr) => {
                let x = self.compile_expression(expr)?;
                let v = self.context.borrow().get_variable(name)?;
                self.copy(&x, &v)?;
                Ok(x)
            }
            ast::Expression::ArrayAssignment(name, index, expr) => {
                let array = self.context.borrow().get_variable(name)?;
                self.mem_write(array.successor(0), index, expr)
            }
            ast::Expression::MemoryRead(addr_expr) => {
                let mem_control_block = self.context.borrow().get_variable(LINMEM)?;
                let adjusted_addr = Box::new(ast::Expression::Binary(
                    addr_expr.clone(),
                    ast::Opcode::Add,
                    Box::new(ast::Expression::Variable(STACKDEPTH)),
                ));
                self.mem_lookup_backwards(mem_control_block.successor(0), &adjusted_addr)
            }
            ast::Expression::MemoryWrite(addr_expr, value_expr) => {
                let mem_control_block = self.context.borrow().get_variable(LINMEM)?;
                let adjusted_addr = Box::new(ast::Expression::Binary(
                    addr_expr.clone(),
                    ast::Opcode::Add,
                    Box::new(ast::Expression::Variable(STACKDEPTH)),
                ));
                self.mem_write_backwards(mem_control_block.successor(0), &adjusted_addr, value_expr)
            }
        };
        self.emitter.newline();
        result
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
                let len = init.len();
                let a = self.context.add_with_size(name, len + array_head_size)?;
                for (i, expr) in init.iter().enumerate() {
                    let value = self.compile_expression(expr)?;
                    let index = a.successor((array_head_size + i) as isize);
                    self.copy(&value, &index)?;
                }
            }
            ast::Statement::If(cond, then, else_) => {
                let cond = self.compile_expression(cond)?;
                let cond = self.wrap_temp(cond)?;
                let t0 = self.context.add_temp()?;
                let t1 = self.context.add_temp()?;
                bf!(&mut self.emitter;
                    t0[-]+
                    t1[-]
                    cond
                );
                self.emitter.newline();
                self.emitter.add_code("[".into())?;
                self.compile(then)?;
                bf!(&mut self.emitter;
                    t0-
                    cond[t1+cond-]
                );
                self.emitter.newline();
                self.emitter.add_code("]".into())?;
                bf!(&mut self.emitter;
                    t1[cond+t1-]
                );
                // else branch
                if let Some(else_) = else_ {
                    self.emitter.newline();
                    bf!(&mut self.emitter;
                        t0
                    );
                    self.emitter.add_code("[".into())?;
                    self.compile(else_)?;
                    bf!(&mut self.emitter;
                        t0[-]
                    );
                    self.emitter.newline();
                    self.emitter.add_code("]".into())?;
                }
            }
            ast::Statement::PutChar(expr) => {
                let e = self.compile_expression(expr)?;
                self.emitter.move_to(&e)?;
                self.emitter.add_code(".".into())?;
            }
            ast::Statement::While(cond, body) => {
                // We do some extra hoops here, to only add the condition code once.
                // See: https://esolangs.org/wiki/Brainfuck_algorithms#while_(x)_{_code_}
                let t = self.context.add_temp()?;
                self.emitter.move_to(&t)?;
                self.emitter.add_code("[-]+[".into())?;
                self.emitter.move_to(&t)?;
                self.emitter.add_code("-".into())?;
                let c = self.context.add_temp()?;
                {
                    let e = self.compile_expression(cond)?;
                    let e = self.wrap_temp(e)?;
                    bf!(&mut self.emitter; mv(e, c));
                    self.emitter.move_to(&c)?;
                }
                self.emitter.add_code("[".into())?;
                self.compile(body)?;
                self.emitter.move_to(&t)?;
                self.emitter.add_code("+".into())?;
                self.emitter.move_to(&c)?;
                self.emitter.add_code("[-]".into())?;
                self.emitter.add_code("]".into())?;
                self.emitter.move_to(&t)?;
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
            ast::Statement::PushStackFrame(vars) => {
                {
                    let vars_in_context = self.context.borrow().get_variable_names();
                    let t = self.context.add_temp()?;
                    let vars_with_values = vars
                        .iter()
                        .map(|(name, e)| (*name, self.compile_expression(e)))
                        .collect::<HashMap<_, _>>();
                    for name in vars_in_context {
                        if name == LINMEM || vars_with_values.contains_key(name.as_str()) {
                            continue;
                        }
                        let v = self.context.borrow().get_variable(name.as_str())?;
                        for i in 0..v.size() {
                            let vi = v.successor(i as isize);
                            let vi_in_stackframe_above = vi.in_stackframe_above();
                            self.copy_using_temp(&vi, &vi_in_stackframe_above, &t)?;
                            self.emitter.newline();
                        }
                    }
                    for (name, value) in vars_with_values.into_iter() {
                        let v = self.context.borrow().get_variable(name)?;
                        let v_in_stackframe_above = v.in_stackframe_above();
                        self.copy_using_temp(&value?, &v_in_stackframe_above, &t)?;
                        self.emitter.newline();
                    }
                }
                let stackdepth = self.context.borrow().get_variable(STACKDEPTH)?;
                self.emitter.move_to(&stackdepth.in_stackframe_above())?;
                self.emitter.add_stackframe_size();
                self.max_stackframe_size = self
                    .max_stackframe_size
                    .max(self.context.borrow().next_adress_after_top());
                self.emitter.stackframe_up();
            }
            ast::Statement::PopStackFrame => {
                self.emitter.stackframe_down();
            }
            ast::Statement::MoveToStackFrameBelow(name) => {
                let v = self.context.borrow().get_variable(name)?;
                let v_in_stackframe_below = v.in_stackframe_below();
                bf!(&mut self.emitter; mv(v, v_in_stackframe_below));
            }
        }
        self.emitter.newline();
        Ok(())
    }
}

pub fn compile_brain_stem(program: &str) -> Result<String> {
    let ops = ProgramParser::new()
        .parse(program)
        .map_err(|e| anyhow!("{}", e))?;
    let mut runtime = Runtime::new();
    for op in ops {
        runtime.compile(&op)?;
    }
    Ok(runtime.emitter.emit(runtime.get_max_stackframe_size()))
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
            runtime.emitter.emit(0),
            "putc(3);
  3
  creating literal 3 into __temp0{5}__temp0{5}>>>>>[-]+++
__temp0{5}.
"
        );
    }

    #[test]
    fn test_putc_not_2() {
        let mut runtime = Runtime::new();
        let expr = ast::Expression::Not(Box::new(ast::Expression::Literal(2)));
        runtime.compile(&&ast::Statement::PutChar(expr)).unwrap();
        assert_eq!(
            runtime.emitter.emit(0),
            "putc(!2);
  !2
    2
    creating literal 2 into __temp0{5}__temp0{5}>>>>>[-]++
  __temp1{6}>[-]+__temp0{5}<[__temp1{6}>-__temp0{5}<[-]]
__temp1{6}>.
"
        );
    }

    #[test]
    fn test_end2end_literal() {
        let bf_code = compile_brain_stem(r#"putc("3");"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "3");
    }

    #[test]
    fn test_end2end_add_sub() {
        let bf_code = compile_brain_stem(r#"putc("0" + 99 - 90);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "9");
    }

    #[test]
    fn test_end2end_mul() {
        let bf_code = compile_brain_stem(r#"putc("0" + 2 * 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "6");
    }

    #[test]
    fn test_end2end_div() {
        let bf_code = compile_brain_stem(r#"putc("0" + 15 / 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(100_000)).unwrap();
        assert_eq!(output, "5");
    }

    #[test]
    fn test_end2end_div_larger() {
        let bf_code = compile_brain_stem(r#"putc("0" + 752 / 100);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000_000)).unwrap();
        assert_eq!(output, "7");
    }

    #[test]
    fn test_end2end_mod() {
        let bf_code = compile_brain_stem(r#"putc("0" + 19 % 12);putc("0" + 23 % 7);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "72");
    }

    #[test]
    fn test_end2end_and() {
        let bf_code =
            compile_brain_stem(r#"putc("0" + (1 && 0));putc("0" + (1 && 7) / (1 && 7));"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "01");
    }

    #[test]
    fn test_end2end_or() {
        let bf_code =
            compile_brain_stem(r#"putc("0" + (0 || 0));putc("0" + (0 || 6) / (0 || 6));"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "01");
    }

    #[test]
    fn test_end2end_lt() {
        let bf_code = compile_brain_stem(
            r#"
            putc("0" + (0 < 17));
            putc("0" + (3 < 2));
            putc("0" + (3 < 3));
        "#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "100");
    }

    #[test]
    fn test_end2end_le() {
        let bf_code = compile_brain_stem(
            r#"putc("0" + (0 <= 17));putc("0" + (3 <= 2));putc("0" + (3 <= 3));"#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "101");
    }

    #[test]
    fn test_end2end_eq() {
        let bf_code = compile_brain_stem(
            r#"putc("0" + (0 == 0));putc("0" + (3 == 3));putc("0" + (3 == 2));"#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "110");
    }

    #[test]
    fn test_end2end_ne() {
        let bf_code = compile_brain_stem(
            r#"putc("0" + (0 != 0));putc("0" + (3 != 3));putc("0" + (3 != 2));"#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "001");
    }

    #[test]
    fn test_end2end_var() {
        let bf_code =
            compile_brain_stem(r#"var x = "0"; putc(x + 2); x = x+1; putc(x + 3);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(output, "24");
    }

    #[test]
    fn test_end2end_array_simple() {
        let bf_code = compile_brain_stem(r#"var s[] = [7]; putc("0" + s[0]);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(100_000)).unwrap();
        assert_eq!(output, "7");
    }

    #[test]
    fn test_end2end_array() {
        let bf_code = compile_brain_stem(
            r#"
            var s[] = "Hello "; 
            putc(s[0]); putc(s[1]); putc(s[2]); putc(s[3]); putc(s[4]); putc(s[5]);
            putc(s[0]); putc(s[1]); putc(s[2]); putc(s[3]); putc(s[4]); putc(s[5]);
            s[4] = "W"; s[3] = "o"; s[2] = "r"; s[1] = "l"; s[0] = "d";
            putc(s[4]); putc(s[3]); putc(s[2]); putc(s[1]); putc(s[0]);
            putc(s[5]);
            putc(s[4]); putc(s[3]); putc(s[2]); putc(s[1]); putc(s[0]); 
        "#,
        )
        .unwrap();
        println!("{}", bf_code);
        let output = run_program_from_str::<u32>(&bf_code, "", Some(1_000_000)).unwrap();
        assert_eq!(output, "Hello Hello World World");
    }



    #[test]
    fn test_block_scope_simple() {
        compile_brain_stem(
            r#"
            var x = 1; { x = 2; }
        "#,
        )
        .unwrap();
    }

    #[test]
    fn test_block_var_not_in_scope() {
        let bf_code = compile_brain_stem(
            r#"
            {var x = 1;} x = 2;
        "#,
        );
        assert_eq!(bf_code.err().unwrap().to_string(), "Variable x not found");
    }

    #[test]
    fn test_end2end_while() {
        let bf_code = compile_brain_stem(
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
    fn test_end2end_while2() {
        let bf_code = compile_brain_stem(
            r#"
                var x = 9;
                while x > 0 {
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
    fn test_end2end_while3() {
        let bf_code = compile_brain_stem(
            r#"
                var x = 0;
                while x < 9 {
                    putc("0" + x);
                    x = x + 1;
                }
            "#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(100_000)).unwrap();
        assert_eq!(output, "012345678");
    }

    #[test]
    fn test_end2end_if_else() {
        let bf_code = compile_brain_stem(
            r#"
                var x = "x";
                if x then {
                    putc("1");
                    putc(x);
                }
                if x then {
                    putc("2");
                    putc(x);
                } else {
                    putc("3");
                    putc(x + 1);
                }
                if !x then {
                    putc("4");
                    putc(x + 1);
                } else {
                    putc("5");
                    putc(x);
                }
            "#,
        )
        .unwrap();
        println!("{}", bf_code);
        let output = run_program_from_str::<u32>(&bf_code, "", Some(100_000)).unwrap();
        assert_eq!(output, "1x2x5x");
    }

    #[test]
    fn test_end2end_linmem_simple() {
        let bf_code = compile_brain_stem(r#"LINMEM[0] = 7; putc("0" + LINMEM[0]);"#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(100_000)).unwrap();
        assert_eq!(output, "7");
    }

    #[test]
    fn test_end2end_linmem() {
        let bf_code =
            compile_brain_stem(r#"
            LINMEM[0] = "H";
            LINMEM[1] = "e";
            LINMEM[2] = "l";
            LINMEM[3] = "l";
            LINMEM[4] = "o";
            LINMEM[5] = " ";
            putc(LINMEM[0]); putc(LINMEM[1]); putc(LINMEM[2]); putc(LINMEM[3]); putc(LINMEM[4]); putc(LINMEM[5]);
            LINMEM[4] = "W";
            LINMEM[3] = "o";
            LINMEM[2] = "r";
            LINMEM[1] = "l";
            LINMEM[0] = "d";
            putc(LINMEM[4]); putc(LINMEM[3]); putc(LINMEM[2]); putc(LINMEM[1]); putc(LINMEM[0]);
        "#).unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(1_000_000)).unwrap();
        assert_eq!(output, "Hello World");
    }

    #[test]
    fn test_push_stack_frame_var_not_found() {
        let bf_code = compile_brain_stem(
            r#"
            PushStackFrame(x=3);
        "#,
        );
        assert_eq!(bf_code.err().unwrap().to_string(), "Variable x not found");
    }

    #[test]
    fn test_push_stack_frame() {
        compile_brain_stem(
            r#"
            var x = 3;
            PushStackFrame(x=4);
        "#,
        )
        .unwrap();
    }

    #[test]
    fn test_pop_stack_frame() {
        let bf_code = compile_brain_stem(
            r#"
            var x = 3;
            PushStackFrame();
            PopStackFrame();
        "#,
        )
        .unwrap();
        assert_eq!(&bf_code[bf_code.len() - 8..bf_code.len()], "\n<<<<<<\n");
    }

    #[test]
    fn test_end2end_push_pop_stack_frame() {
        let bf_code = compile_brain_stem(
            r#"
            var x = "0";
            putc(x);
            PushStackFrame(x=x+1);
            putc(x);
            PushStackFrame(x=x+1);
            putc(x);
            PopStackFrame();
            putc(x);
            PopStackFrame();
            putc(x);
        "#,
        )
        .unwrap();
        let result = run_program_from_str::<u32>(&bf_code, "", Some(10_000)).unwrap();
        assert_eq!(result, "01210");
    }

    #[test]
    fn test_move_to_stack_frame_below() {
        compile_brain_stem(
            r#"
            var x = 3;
            PushStackFrame();
            MoveToStackFrameBelow(x);
        "#,
        )
        .unwrap();
    }

    #[test]
    fn test_end2end_recursive_number_printer() {
        let bf_code = compile_brain_stem(
            r#"
            var n = 752;
            var depth = 1;
            var base = 10;

            while depth {
                if n >= base then {
                    var q = n / base;
                    n = n % base;
                    PushStackFrame(n=q, depth=depth + 1);
                } else {
                    putc("0" + n);
                    if depth then {
                        PopStackFrame();
                    }
                }
            }
        "#,
        )
        .unwrap();
        let output = run_program_from_str::<u32>(&bf_code, "", Some(10_000_000)).unwrap();
        assert_eq!(output, "752");
    }

    #[test]
    fn test_end2end_linmem_and_stackframes() {
        let bf_code = compile_brain_stem(
            r#"
            var x = 0;
            LINMEM[10] = "1";
            LINMEM[20] = "2";
            LINMEM[30] = "3";
            PushStackFrame(x=x+1);
            PushStackFrame(x=x+1);
            putc(LINMEM[10] + x);
            putc(LINMEM[20] + x);
            putc(LINMEM[30] + x);
            putc("X");
            PopStackFrame();
            putc(LINMEM[10] + x);
            putc(LINMEM[20] + x);
            putc(LINMEM[30] + x);
            putc("X");
            PopStackFrame();
            putc(LINMEM[10] + x);
            putc(LINMEM[20] + x);
            putc(LINMEM[30] + x);
            putc("X");
        "#,
        )
        .unwrap();
        let result = run_program_from_str::<u32>(&bf_code, "", Some(300_000)).unwrap();
        assert_eq!(result, "345X234X123X");
    }
}
