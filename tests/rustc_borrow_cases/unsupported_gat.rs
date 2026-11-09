trait Project {type Ref<'a> where Self:'a;fn get<'a>(&'a self)->Self::Ref<'a>;}
struct Holder(i64);
impl Project for Holder {type Ref<'a>=&'a i64 where Self:'a;fn get<'a>(&'a self)->Self::Ref<'a>{&self.0}}
pub fn probe(){let h=Holder(1);let _=h.get();}
