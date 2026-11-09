struct Cell(i64);
impl Cell {fn get(&self)->i64{self.0} fn inc(&mut self){self.0+=1;}}
pub fn probe(){let mut c=Cell(1);let _=c.get();c.inc();}
