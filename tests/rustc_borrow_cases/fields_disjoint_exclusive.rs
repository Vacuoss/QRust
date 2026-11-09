struct Pair{x:i64,y:i64}
pub fn probe(){let mut p=Pair{x:1,y:2};let a=&mut p.x;let b=&mut p.y;*a=7;*b=8;}
