//Compact, strongly typed IDs
use std::collections::HashMap;
use std::rc::Rc;
use crate::syntax::Name;

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct QubitId(pub u32);
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct BitId(pub u32);

#[derive(Debug)]
pub struct SymbolTable<T: Copy> {
    names: HashMap<String, SymbolId>,
    slots: Vec<T>,
}
impl<T: Copy> SymbolTable<T> {
    pub fn with_capacity(n: usize) -> Self {
        Self { names: HashMap::with_capacity(n), slots: Vec::with_capacity(n) }
    }
    pub fn contains_key(&self, name: &str) -> bool { self.names.contains_key(name) }
    pub fn id(&self, name: &str) -> Option<SymbolId> { self.names.get(name).copied() }
    pub fn by_id(&self, id: SymbolId) -> T { self.slots[id.0 as usize] }
    pub fn get(&self, name: &str) -> Option<T> { self.id(name).map(|id| self.by_id(id)) }
    pub fn insert(&mut self, name: &str, value: T) -> SymbolId {
        if let Some(&id) = self.names.get(name) {
            self.slots[id.0 as usize] = value;
            return id;
        }
        let id = SymbolId(u32::try_from(self.slots.len()).expect("too many symbols"));
        self.names.insert(name.to_owned(), id);
        self.slots.push(value);
        id
    }
    #[cfg(test)]
    pub fn slot_count(&self) -> usize { self.slots.len() }
}

#[derive(Default, Debug)]
pub struct NameInterner {
    by_name: HashMap<Rc<str>, SymbolId>,
    names: Vec<Rc<str>>,
}
impl NameInterner {
    pub fn id(&self, name: &str) -> Option<SymbolId> {
        self.by_name.get(name).copied()
    }
    pub fn intern(&mut self, name: &str) -> SymbolId {
        if let Some(id) = self.id(name) { return id; }
        let id = SymbolId(u32::try_from(self.names.len()).expect("symbol ID space exhausted"));
        let shared: Rc<str> = Rc::from(name);
        self.by_name.insert(Rc::clone(&shared), id);
        self.names.push(shared);
        id
    }
    pub fn name(&self, id: SymbolId) -> &str { &self.names[id.0 as usize] }
    pub fn shared_name(&self, id: SymbolId) -> Name {
        Name::from(Rc::clone(&self.names[id.0 as usize]))
    }
    #[cfg(test)]
    pub fn len(&self) -> usize { self.names.len() }
}

#[cfg(test)]
mod output_name_tests {
    use super::*;
    #[test]
    fn symbol_handles_share_storage_and_outlive_the_interner() {
        let (first, second) = {
            let mut names = NameInterner::default();
            let id = names.intern("a_very_long_quantum_variable_name");
            assert_eq!(names.intern("a_very_long_quantum_variable_name"), id);
            let a = names.shared_name(id);
            let b = names.shared_name(id);
            assert!(a.shares_storage_with(&b));
            (a, b)
        };
        assert_eq!(first.as_str(), "a_very_long_quantum_variable_name");
        assert!(first.shares_storage_with(&second));
    }
    #[test]
    fn symbol_ids_and_shadowed_spelling_are_stable() {
        let mut names = NameInterner::default();
        let a = names.intern("q");
        let b = names.intern("__qrust_2_q");
        assert_ne!(a, b);
        assert_eq!(names.id("q"), Some(a));
        assert_eq!(names.name(b), "__qrust_2_q");
        assert!(!names.shared_name(a).shares_storage_with(&names.shared_name(b)));
    }
}
