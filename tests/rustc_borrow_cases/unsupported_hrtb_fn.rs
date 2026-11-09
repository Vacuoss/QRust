fn apply<F:for<'a> Fn(&'a i64)->i64>(f:F)->i64{f(&41)}
pub fn probe(){let _=apply(|x|*x+1);}
