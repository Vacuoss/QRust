pub fn probe(){let mut n=1_i64;let a=&mut n;let b=&mut *a;let c=&mut *b;*c=11;let x=*c;*b=12;let y=*b;*a=13;let z=*a;let _=(x,y,z);}
