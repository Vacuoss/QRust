pub fn identity<'a>(x:&'a mut i64)->&'a mut i64{x}
pub fn probe(){let mut n=3_i64;let r=identity(&mut n);n=5;let _=*r;}
