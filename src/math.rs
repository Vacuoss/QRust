//Deterministic compile-time floating-point math

pub const FUNCTIONS: &[(&str, usize)] = &[
    ("sin",1),("cos",1),("tan",1),("asin",1),("acos",1),("atan",1),
    ("sinh",1),("cosh",1),("tanh",1),("asinh",1),("acosh",1),("atanh",1),
    ("sqrt",1),("cbrt",1),("abs",1),("exp",1),("exp2",1),
    ("ln",1),("log2",1),("log10",1),
    ("floor",1),("ceil",1),("round",1),("trunc",1),("fract",1),("signum",1),
    ("radians",1),("degrees",1),
    ("pow",2),("atan2",2),("hypot",2),("min",2),("max",2),
    ("clamp",3),
];

pub fn canonical(name: &str) -> &str {
    match name {
        "arcsin" => "asin", "arccos" => "acos", "arctan" => "atan",
        "log" => "ln", "ceiling" => "ceil", "power" => "pow",
        "deg2rad" | "to_radians" => "radians",
        "rad2deg" | "to_degrees" => "degrees",
        _ => name,
    }
}

pub fn arity(name: &str) -> Option<usize> {
    Some(match canonical(name) {
        "sin" | "cos" | "tan" | "asin" | "acos" | "atan" |
        "sinh" | "cosh" | "tanh" | "asinh" | "acosh" | "atanh" |
        "sqrt" | "cbrt" | "abs" | "exp" | "exp2" | "ln" | "log2" | "log10" |
        "floor" | "ceil" | "round" | "trunc" | "fract" | "signum" |
        "radians" | "degrees" => 1,
        "pow" | "atan2" | "hypot" | "min" | "max" => 2,
        "clamp" => 3,
        _ => return None,
    })
}

pub fn evaluate(name: &str, a: &[f64]) -> Result<f64, &'static str> {
    let f = canonical(name);
    let x = a[0];
    let value = match f {
        "sin" => x.sin(), "cos" => x.cos(), "tan" => x.tan(),
        "asin" => x.asin(), "acos" => x.acos(), "atan" => x.atan(),
        "sinh" => x.sinh(), "cosh" => x.cosh(), "tanh" => x.tanh(),
        "asinh" => x.asinh(), "acosh" => x.acosh(), "atanh" => x.atanh(),
        "sqrt" => x.sqrt(), "cbrt" => x.cbrt(), "abs" => x.abs(),
        "exp" => x.exp(), "exp2" => x.exp2(),
        "ln" => x.ln(), "log2" => x.log2(), "log10" => x.log10(),
        "floor" => x.floor(), "ceil" => x.ceil(), "round" => x.round(),
        "trunc" => x.trunc(), "fract" => x.fract(), "signum" => x.signum(),
        "radians" => x.to_radians(), "degrees" => x.to_degrees(),
        "pow" => x.powf(a[1]), "atan2" => x.atan2(a[1]),
        "hypot" => x.hypot(a[1]), "min" => x.min(a[1]), "max" => x.max(a[1]),
        "clamp" => {
            if a[1] > a[2] { return Err("clamp minimum must not exceed maximum"); }
            x.clamp(a[1], a[2])
        }
        _ => return Err("unknown mathematical function"),
    };
    if value.is_finite() { Ok(value) }
    else { Err("non-finite result in numeric expression (check function domain or overflow)") }
}
