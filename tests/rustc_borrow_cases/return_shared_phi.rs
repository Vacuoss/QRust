pub fn choose<'a>(pick:bool,left:&'a i64,right:&'a i64)->&'a i64{if pick{left}else{right}}
pub fn probe(){let a=4_i64;let b=9_i64;let r=choose(false,&a,&b);let _=*r;}
