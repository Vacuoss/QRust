struct P{x:i64}
pub fn probe(){let mut p=P{x:1};let a=&mut p.x;let b=&mut p.x;*a=3;*b=4;}
