use anyhow::{Result, anyhow, bail};
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Error, Formatter};
use std::rc::{Rc, Weak};

pub trait VariableLike: Debug {
    fn address(&self) -> isize;
}

pub struct Variable {
    name: String,
    is_temp: bool,
    address: isize,
    size: usize,
    // Store a weak reference to avoid a reference cycle.
    context: Weak<RefCell<Context>>,
}

impl Variable {
    pub fn is_temp(&self) -> bool {
        self.is_temp
    }
}

impl Debug for Variable {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        if self.size == 1 {
            write!(fmt, "{}{{{}}}", self.name, self.address)
        } else {
            write!(fmt, "{}{{{};{}}}", self.name, self.address, self.size)
        }
    }
}

impl VariableLike for Variable {
    fn address(&self) -> isize {
        self.address
    }
}

impl VariableLike for Rc<Variable> {
    fn address(&self) -> isize {
        self.address
    }
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

pub trait VariableExt {
    fn predecessor(&self) -> Successor;
    fn successor(&self, offset: usize) -> Successor;
}

impl VariableExt for Rc<Variable> {
    fn predecessor(&self) -> Successor {
        Successor {
            original: self.clone(),
            offset: -1,
        }
    }
    fn successor(&self, offset: usize) -> Successor {
        Successor {
            original: self.clone(),
            offset: offset as isize,
        }
    }
}

pub struct Successor {
    original: Rc<Variable>,
    offset: isize,
}

impl Debug for Successor {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), Error> {
        let neg = if self.offset < 0 { "neg" } else { "" };
        write!(
            fmt,
            "Successor({:?}; {}{})",
            self.original,
            neg,
            self.offset.abs()
        )
    }
}

impl VariableLike for Successor {
    fn address(&self) -> isize {
        self.original.address + self.offset
    }
}

pub trait AsVariableLikeRef<'a> {
    // Associated type: The concrete type T that implements VariableLike
    // We need this because copy is generic over T, not dyn VariableLike
    type Target: VariableLike + 'a;

    fn as_variable_like_ref(&'a self) -> &'a Self::Target;
}

// --- Implement the Helper Trait for Expected Input Types ---

// 1. Implement for Rc<Variable>
impl<'a> AsVariableLikeRef<'a> for Rc<Variable> {
    type Target = Variable; // The T for copy will be Variable
    fn as_variable_like_ref(&'a self) -> &'a Variable {
        // Dereference the Rc to get the underlying Variable
        &**self // Equivalent to self.as_ref() or &*self.deref()
    }
}

// 2. Implement for Variable itself
// This handles cases where you pass `&Variable`. The method call `var_ref.as_variable_like_ref()`
// will implicitly dereference var_ref (from &Variable to Variable) and call this impl.
impl<'a> AsVariableLikeRef<'a> for Variable {
    type Target = Variable; // The T for copy will be Variable
    fn as_variable_like_ref(&'a self) -> &'a Variable {
        // 'self' is already the &Variable we need
        self
    }
}

// 3. Implement for other VariableLike types (e.g., Successor) if needed
impl<'a> AsVariableLikeRef<'a> for Successor {
    type Target = Successor; // The T for copy will be Successor
    fn as_variable_like_ref(&'a self) -> &'a Successor {
        self
    }
}

#[derive(Debug)]
pub struct Context {
    variables: HashMap<String, Weak<Variable>>,
    used_addresses: HashSet<isize>,
    temp_count: usize,
    scoped_variable_store: Vec<Vec<Rc<Variable>>>,
}

impl Context {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            variables: HashMap::new(),
            used_addresses: HashSet::new(),
            temp_count: 0,
            scoped_variable_store: vec![Vec::new()],
        }))
    }

    pub fn get_variable(&self, name: &str) -> Option<Rc<Variable>> {
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

    pub fn push_scope(&mut self) {
        self.scoped_variable_store.push(Vec::new());
    }

    pub fn pop_scope(&mut self) -> Result<()> {
        let scoped_vars = self.scoped_variable_store.pop();
        if scoped_vars.is_none() {
            return Err(anyhow!("No scope to pop"));
        }
        // We need to manually drop the variables in the current scope.
        // Otherwise they would try to deregister themselves when they go out of scope, while we still hold the borrow_mut.
        // This would fail, because they would also try to borrow_mut the context.
        for mut var in scoped_vars.unwrap() {
            self.deregister(&var.name, var.address, var.size)?;
            Rc::get_mut(&mut var).unwrap().context = Weak::new(); // Clear the context reference
        }
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
        let v = match ctx.variables.entry(name.to_string()) {
            Entry::Occupied(_) => bail!("Variable {} already exists", name),
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
                variable
            }
        };
        if !is_temp {
            ctx.scoped_variable_store
                .last_mut()
                .unwrap()
                .push(v.clone());
        }
        Ok(v)
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
