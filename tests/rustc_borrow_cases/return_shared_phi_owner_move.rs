struct Blob{n:i64}
struct Tri{a:Blob,b:Blob}
pub fn probe(flag:bool){let t=Tri{a:Blob{n:1},b:Blob{n:2}};let r=if flag{&t.a}else{&t.b};let stolen=t.a;let _=(r.n,stolen.n);}
