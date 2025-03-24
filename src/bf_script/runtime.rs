use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

#[derive(Debug)]
pub struct Variable {
    name: String,
    address: isize,
    size: usize,
}

#[derive(Debug)]
pub struct Context {
    parent: Option<Box<Context>>,
    variables: HashMap<String, Weak<Variable>>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            parent: None,
            variables: HashMap::new(),
        }
    }

    pub fn add(&mut self, name: &str, size: usize) -> Rc<Variable> {
        let address = self.find_next_free(size);
        let variable = Rc::new(Variable {
            name: name.to_string(),
            address,
            size,
        });
        self.variables
            .insert(name.to_string(), Rc::downgrade(&variable));
        variable
    }

    pub fn find_next_free(&mut self, size: usize) -> isize {
        self.cleanup_stale();
        let top_address = self
            .variables
            .values()
            .map(|v| v.upgrade().unwrap())
            .map(|v| v.address + v.size as isize)
            .max()
            .unwrap_or(0);
        let used_addresses: HashSet<isize> = self
            .variables
            .values()
            .map(|v| v.upgrade().unwrap())
            .map(|v| v.address..v.address + v.size as isize)
            .flat_map(|r| r)
            .collect();
        let mut address = 0;
        while address < top_address {
            let mut is_free = true;
            for i in 0..size {
                if used_addresses.contains(&(address + i as isize)) {
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

    pub fn cleanup_stale(&mut self) {
        self.variables.retain(|_, v| v.strong_count() > 0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_variable() {
        let mut context = Context::new();
        let var1 = context.add("var1", 4);
        let var2 = context.add("var2", 2);

        assert_eq!(var1.name, "var1");
        assert_eq!(var1.size, 4);
        assert_eq!(var1.address, 0);

        assert_eq!(var2.name, "var2");
        assert_eq!(var2.size, 2);
        assert_eq!(var2.address, 4);
    }

    #[test]
    fn test_find_next_free() {
        let mut context = Context::new();
        let _v1 = context.add("var1", 4);
        {
            let _v2 = context.add("var2", 2);

            assert_eq!(context.find_next_free(3), 6); // Address after var2
        }
        // var2 goes out of scope
        assert_eq!(context.find_next_free(3), 4); // Address after var1
    }
}
