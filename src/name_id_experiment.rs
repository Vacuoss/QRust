//Experimental compact lexical names; test-only and not wired into AST
use std::{collections::HashMap, rc::Rc};
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NameId(pub u32);

#[derive(Default)]
pub struct NamePool {
    lookup: HashMap<Rc<str>, NameId>,
    storage: Vec<Rc<str>>,
}
impl NamePool {
    pub fn intern(&mut self, spelling: &str) -> NameId {
        if let Some(&id) = self.lookup.get(spelling) { return id; }
        let id = NameId(u32::try_from(self.storage.len()).expect("NameId pool overflow"));
        let value: Rc<str> = Rc::from(spelling);
        self.lookup.insert(Rc::clone(&value), id);
        self.storage.push(value);
        id
    }
    pub fn get(&self, id: NameId) -> Option<&str> {
        self.storage.get(id.0 as usize).map(|n| n.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn name_id_is_compact_but_needs_a_lifetime_owner() {
        assert_eq!(std::mem::size_of::<NameId>(), 4);
        assert!(std::mem::size_of::<crate::syntax::Name>() > 4);
        let mut pool = NamePool::default();
        let a = pool.intern("q");
        assert_eq!(a, pool.intern("q"));
        let b = pool.intern("__qrust_internal_q");
        assert_ne!(a, b);
        assert_eq!(pool.get(a), Some("q"));
        assert_eq!(pool.get(b), Some("__qrust_internal_q"));
        assert_eq!(pool.get(NameId(u32::MAX)), None);
    }
}
