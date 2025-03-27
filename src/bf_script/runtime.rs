use anyhow::{Result, anyhow};
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};
use super::ast;

#[derive(Debug)]
pub struct Variable {
    name: String,
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

    fn deregister(&mut self, name: &str, address: isize, size: usize) -> Result<()> {
        for i in 0..size {
            self.used_addresses.remove(&(address + i as isize));
        }
        self.variables.remove(name);
        Ok(())
    }

    fn add_impl(context: &Rc<RefCell<Self>>, name: &str, size: usize) -> Result<Rc<Variable>> {
        let weak_ctx = Rc::downgrade(context);
        let mut ctx = context.borrow_mut();
        let address = ctx.find_next_free(size);
        match ctx.variables.entry(name.to_string()) {
            Entry::Occupied(_) => Err(anyhow!("Variable {} already exists", name)),
            Entry::Vacant(entry) => {
                let variable = Rc::new(Variable {
                    name: name.to_string(),
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
        Self::add_impl(context, &name, size)
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
}

impl ContextExt for Rc<RefCell<Context>> {
    fn add_with_size(&self, name: &str, size: usize) -> Result<Rc<Variable>> {
        Context::add_impl(self, name, size)
    }
    fn add(&self, name: &str) -> Result<Rc<Variable>> {
        Context::add_impl(self, name, 1)
    }
    fn add_temp(&self) -> Result<Rc<Variable>> {
        Context::add_temp_impl(self, 1)
    }
}


static VALID_BF_CHARS: &str = "+-<>[],.";


#[derive(Debug)]
enum Item {
    Verbatim(String),
    Indent,
    Dedent,
}

#[derive(Debug)]
struct Emitter {
    items: Vec<Item>,
}

impl Emitter {
    pub fn new() -> Self {
        Self { items: Vec::new() }
    }

    pub fn add_code(&mut self, code: String) -> Result<()> {
        if code.chars().any(|c| !VALID_BF_CHARS.contains(c)) {
            return Err(anyhow!("Invalid character in code: {}", code));
        }
        self.items.push(Item::Verbatim(code));
        Ok(())
    }

    pub fn add_comment(&mut self, comment: String) -> Result<()> {
        if comment.chars().any(|c| VALID_BF_CHARS.contains(c)) {
            return Err(anyhow!("Code character in comment: {}", comment));
        }
        self.items.push(Item::Verbatim(comment));
        Ok(())
    }

    pub fn emit(&self) -> String {
        let mut indent = 0;
        static INDENTATION: &str = "  ";
        self.items
            .iter()
            .map(|item| match item {
                Item::Verbatim(code) => Some(INDENTATION.repeat(indent) + code),
                Item::Indent => {
                    indent += 1;
                    None
                }
                Item::Dedent => {
                    indent -= 1;
                    None
                }
            }).filter(|x| x.is_some())
            .map(|x| x.unwrap())
            .collect()
    }
}



#[derive(Debug)]
struct Runtime {
    context: Rc<RefCell<Context>>,
    current_address: isize,
    emitter: Emitter,
}

impl Runtime {
    pub fn new() -> Self {
        Self {
            context: Context::new(),
            current_address: 0,
            emitter: Emitter::new(),
        }
    }

    fn compile_expression(&mut self, expr: &ast::Expression) -> Result<Rc<Variable>> {
        let t = self.context.add_temp()?;
        match expr {
            ast::Expression::Literal(_) => {
                // Allocate space for the literal.
            }
            ast::Expression::Unary(_, expr) => {
                // Compile the expression.
            }
            ast::Expression::Binary(lhs, _, rhs) => {
                // Compile the left-hand side.
                // Compile the right-hand side.
            }
            ast::Expression::Variable(name) => {
                // Look up the variable in the context.
            }
            ast::Expression::IndexedVariable(name, index) => {
                // Compile the index expression.
                // Look up the variable in the context.
            }
            ast::Expression::Assignment(name, expr) => {
                // Compile the expression.
                // Look up the variable in the context.
            }
            ast::Expression::IndexedAssignment(name, index, expr) => {
                // Compile the index expression.
                // Compile the expression.
                // Look up the variable in the context.
            }
        }
        Ok(t)
    }

    fn move_to(&mut self, v: &Variable) -> Result<()> {
        let diff = v.address - self.current_address;
        if diff > 0 {
            self.emitter.add_code("+".repeat(diff as usize))?;
        } else if diff < 0 {
            self.emitter.add_code("-".repeat(-diff as usize))?;
        }
        self.current_address = v.address;
        Ok(())
    }

    pub fn compile(&mut self, statement: &ast::Statement) -> Result<()> {
        match statement {
            ast::Statement::VarDeclaration(name, size) => {
                // let var = self.context.add(name, size.len())?;
                // for (i, expr) in size.iter().enumerate() {
                //     // Compile the expression and store the result in the variable.
                // }
            }
            ast::Statement::If(cond, then, else_) => {
                // Compile the condition.
                // Compile the then branch.
                // Compile the else branch if it exists.
            }
            ast::Statement::PutChar(expr) => {
                let e = self.compile_expression(expr)?;
                self.move_to(&e)?;
                self.emitter.add_code(".".into())?;
            }
            ast::Statement::While(cond, body) => {
                // Compile the condition.
                // Compile the body.
            }
            ast::Statement::Block(statements) => {
                // Compile each statement in the block.
            }
            ast::Statement::Expression(expr) => {
                // Compile the expression.
            }
        }
        Ok(())
    }

}


#[cfg(test)]
mod tests {
    use super::*;

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
}
