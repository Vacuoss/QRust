struct Guard<'a>(&'a mut i64);
impl Drop for Guard<'_>{fn drop(&mut self){*self.0+=1;}}
pub fn probe(){let mut x=1;let _guard=Guard(&mut x);}
