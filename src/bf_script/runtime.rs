use anyhow::{Result, anyhow};
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

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
    fn add(&self, name: &str, size: usize) -> Result<Rc<Variable>>;
    fn add_temp(&self, size: usize) -> Result<Rc<Variable>>;
}

impl ContextExt for Rc<RefCell<Context>> {
    fn add(&self, name: &str, size: usize) -> Result<Rc<Variable>> {
        Context::add_impl(self, name, size)
    }
    fn add_temp(&self, size: usize) -> Result<Rc<Variable>> {
        Context::add_temp_impl(self, size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let ctx = Context::new();
        let var1 = ctx.add("var1", 4).unwrap();
        let var2 = ctx.add("var2", 2).unwrap();

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
        let _var1 = ctx.add("foo", 4).unwrap();
        assert!(ctx.add("foo", 2).is_err());
    }

    #[test]
    fn test_add_after_drop() {
        let ctx = Context::new();
        let _v1 = ctx.add("var1", 4);
        {
            let _v2 = ctx.add_temp(2);
            assert_eq!(ctx.add_temp(3).unwrap().address, 6); // Address after var2
        }
        // var2 goes out of scope
        assert_eq!(ctx.add_temp(3).unwrap().address, 4); // Address after var1
    }
}
