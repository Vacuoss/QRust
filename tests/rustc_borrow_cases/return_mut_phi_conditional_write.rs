struct Blob{n:i64} struct Tri{a:Blob,b:Blob}
fn choose<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{if flag{&mut t.a}else{&mut t.b}}
fn set_n(x:&mut Blob){x.n=9;}
pub fn probe(flag:bool){let mut t=Tri{a:Blob{n:1},b:Blob{n:2}};let r=choose(flag,&mut t);set_n(r);let _=r.n;}
