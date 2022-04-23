#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unused_assignments,
    unused_mut
)]

use std::{
    alloc::{alloc_zeroed, dealloc, Layout},
    error,
    ffi::{CStr, CString},
    fmt, mem,
    process::exit,
    ptr,
};

use gpoint::GPoint;

#[derive(Eq, Debug, PartialEq)]
enum LexError {
    Eof,
    IdTooLong,

    InvalidUtf8 { cause: std::str::Utf8Error },

    IoError,
    Dangling,
    UnexpectedChar(char),
}

impl LexError {
    fn to_cstring(&self) -> CString {
        CString::new(self.to_string()).unwrap()
    }
}

impl error::Error for LexError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            LexError::InvalidUtf8 { cause } => Some(cause),
            _ => None,
        }
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LexError::Eof => write!(f, "reached end of file"),
            LexError::IdTooLong => write!(f, "identifier too long"),
            LexError::InvalidUtf8 { cause } => write!(f, "invalid UTF-8: {}", cause),
            LexError::IoError => write!(f, "I/O error"),
            LexError::Dangling => write!(f, "uninitialized"),
            LexError::UnexpectedChar(c) => write!(f, "unexpected character: {}", c),
        }
    }
}

#[derive(Debug)]
enum Error {
    LexError { source: LexError },
    MalformedUnicode,
    ParseError(String),
    UnknownConstant { name: String },
    UnknownFunction { name: String },
    ValueError(String),
}

macro_rules! parse_error {
    ($($arg:tt)*) => {{
        $crate::Error::ParseError(format!($($arg)*))
    }}
}

impl Error {
    pub fn expect(wanted: &str, got: Token) -> Self {
        Self::ParseError(format!("expecting {}, got '{}'", wanted, got))
    }
}

impl From<LexError> for Error {
    fn from(source: LexError) -> Self {
        Self::LexError { source }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Error::LexError { source } => Some(source),
            _ => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;

        match self {
            LexError { source } => write!(f, "{}", source),
            MalformedUnicode => write!(f, "malformed unicode detected"),
            ParseError(s) => write!(f, "parse error: {}", s),
            UnknownConstant { name } => write!(f, "unknown constant: {}", name),
            UnknownFunction { name } => {
                write!(f, "unknown function '{}'", name)
            }
            ValueError(s) => write!(f, "value error: {}", s),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Constant {
    E,
    Pi,
}

impl From<Constant> for f64 {
    fn from(c: Constant) -> f64 {
        use std::f64::consts;
        use Constant::*;

        match c {
            E => consts::E,
            Pi => consts::PI,
        }
    }
}

impl TryFrom<&str> for Constant {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        use Constant::*;

        match s {
            "e" => Ok(E),
            "pi" => Ok(Pi),
            _ => Err(Error::UnknownConstant {
                name: s.to_string(),
            }),
        }
    }
}

impl TryFrom<&CStr> for Constant {
    type Error = Error;

    fn try_from(s: &CStr) -> Result<Self, Self::Error> {
        s.to_str()
            .map_err(|_| Error::MalformedUnicode)
            .and_then(Self::try_from)
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl Constant {
    pub fn cname(&self) -> CString {
        CString::new(self.name()).expect("conversion to CString failed")
    }

    pub fn name(&self) -> &'static str {
        use Constant::*;

        match self {
            E => "e",
            Pi => "pi",
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Func {
    Atan,
    Cos,
    Ln,
    Log,
    Log2,
    Round,
    Sin,
    Tan,
}

impl TryFrom<&str> for Func {
    type Error = Error;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        match s {
            "atan" => Ok(Func::Atan),
            "cos" => Ok(Func::Cos),
            "ln" => Ok(Func::Ln),
            "log" => Ok(Func::Log),
            "log2" => Ok(Func::Log2),
            "round" => Ok(Func::Round),
            "sin" => Ok(Func::Sin),
            "tan" => Ok(Func::Tan),
            _ => Err(Error::UnknownFunction {
                name: s.to_string(),
            }),
        }
    }
}

impl TryFrom<&CStr> for Func {
    type Error = Error;

    fn try_from(s: &CStr) -> Result<Self, Self::Error> {
        s.to_str()
            .map_err(|_| Error::MalformedUnicode)
            .and_then(Self::try_from)
    }
}

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl Func {
    pub fn eval(self, x: f64) -> f64 {
        use Func::*;

        match self {
            Atan => x.atan(),
            Cos => x.cos(),
            Ln => x.ln(),
            Log => x.log10(),
            Log2 => x.log2(),
            Round => x.round(),
            Sin => x.sin(),
            Tan => x.tan(),
        }
    }

    fn cname(self) -> CString {
        CString::new(self.name()).expect("conversion to CString failed")
    }

    pub fn name(self) -> &'static str {
        match self {
            Func::Atan => "atan",
            Func::Cos => "cos",
            Func::Ln => "ln",
            Func::Log => "log",
            Func::Log2 => "log2",
            Func::Round => "round",
            Func::Sin => "sin",
            Func::Tan => "tan",
        }
    }
}

enum LexState {
    Ok,
}

enum Node {
    Binary {
        op: BinaryOp,
        lhs: Box<Node>,
        rhs: Box<Node>,
    },
    Call {
        func: Func,
        args: Vec<Node>,
    },
    Unary {
        op: UnaryOp,
        rhs: Box<Node>,
    },
    Value(Value),
}

enum BinaryOp {
    Div,
    Pow,
    Plus,
    Minus,
    Times,
}

#[derive(Eq, PartialEq)]
enum OpArity {
    Binary,
    None,
    Unary,
}

#[derive(Eq, PartialEq)]
enum OpAssoc {
    Left,
    None,
    Right,
}

type OpPrec = i8;

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Div,
    Minus,
    Number(f64),
    Plus,
    Times,
    Newline,
    OPar,
    CPar,
    Caret,
    Id(String),
}

impl Token {
    const fn arity(&self) -> OpArity {
        use Token::*;

        match self {
            Div | Minus | Plus | Times | Caret => OpArity::Binary,
            Number(_) | Newline | OPar | CPar | Id(_) => OpArity::None,
        }
    }

    const fn assoc(&self) -> OpAssoc {
        use Token::*;

        match self {
            Div | Minus | Plus | Times => OpAssoc::Left,
            Number(_) | Newline | OPar | CPar | Id(_) => OpAssoc::None,
            Caret => OpAssoc::Right,
        }
    }

    const fn prec(&self) -> OpPrec {
        use Token::*;

        match self {
            Div => 2,
            Minus => 1,
            Plus => 1,
            Times => 2,
            Caret => 3,
            _ => -1,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Token::*;

        match self {
            Div => write!(f, "/"),
            Minus => write!(f, "-"),
            Number(n) => write!(f, "{}", GPoint(*n)),
            Plus => write!(f, "+"),
            Times => write!(f, "*"),
            Newline => write!(f, "\\n"),
            OPar => write!(f, "("),
            CPar => write!(f, ")"),
            Caret => write!(f, "^"),
            Id(str) => write!(f, "{}", str),
        }
    }
}

enum UnaryOp {
    Neg,
}

#[derive(Clone, Copy, Debug)]
enum Value {
    Constant(Constant),
    Number(f64),
    Func(Func),
}

impl TryFrom<Value> for f64 {
    type Error = Error;

    fn try_from(v: Value) -> Result<Self, Self::Error> {
        match v {
            Value::Constant(c) => Ok(c.into()),
            Value::Number(n) => Ok(n),
            Value::Func(f) => Err(Error::ValueError(format!(
                "function '{}' cannot be converted to a number",
                f.name()
            ))),
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Value::*;

        match *self {
            Constant(c) => write!(f, "{}", c),
            Number(n) => write!(f, "{}", GPoint(n)),
            Func(func) => write!(f, "{}", func),
        }
    }
}

impl Value {
    pub fn eval(self, some_x: Option<f64>) -> f64 {
        use Value::*;

        match self {
            Constant(c) => c.into(),
            Number(n) => n,
            Func(f) => f.eval(some_x.unwrap()),
        }
    }

    pub fn to_cstring(&self) -> CString {
        CString::new(self.to_string()).expect("conversion to CString failed")
    }
}

extern "C" {
    fn __ctype_b_loc() -> *mut *const libc::c_ushort;

    fn _IO_getc(__fp: *mut _IO_FILE) -> libc::c_int;

    static mut stdin: *mut _IO_FILE;

    static mut stdout: *mut _IO_FILE;

    fn fclose(__stream: *mut FILE) -> libc::c_int;

    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;

    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;

    fn ferror(__stream: *mut FILE) -> libc::c_int;

    fn fputs(__s: *const libc::c_char, __stream: *mut FILE) -> libc::c_int;

    fn puts(__s: *const libc::c_char) -> libc::c_int;

    fn ungetc(__c: libc::c_int, __stream: *mut FILE) -> libc::c_int;
}

type __off_t = libc::c_long;
type __off64_t = libc::c_long;
type C2RustUnnamed = libc::c_uint;
const _ISalnum: C2RustUnnamed = 8;
const _ISpunct: C2RustUnnamed = 4;
const _IScntrl: C2RustUnnamed = 2;
const _ISblank: C2RustUnnamed = 1;
const _ISgraph: C2RustUnnamed = 32768;
const _ISprint: C2RustUnnamed = 16384;
const _ISspace: C2RustUnnamed = 8192;
const _ISxdigit: C2RustUnnamed = 4096;
const _ISdigit: C2RustUnnamed = 2048;
const _ISalpha: C2RustUnnamed = 1024;
const _ISlower: C2RustUnnamed = 512;
const _ISupper: C2RustUnnamed = 256;

#[derive(Copy, Clone)]
#[repr(C)]
struct _IO_FILE {
    pub _flags: libc::c_int,
    pub _IO_read_ptr: *mut libc::c_char,
    pub _IO_read_end: *mut libc::c_char,
    pub _IO_read_base: *mut libc::c_char,
    pub _IO_write_base: *mut libc::c_char,
    pub _IO_write_ptr: *mut libc::c_char,
    pub _IO_write_end: *mut libc::c_char,
    pub _IO_buf_base: *mut libc::c_char,
    pub _IO_buf_end: *mut libc::c_char,
    pub _IO_save_base: *mut libc::c_char,
    pub _IO_backup_base: *mut libc::c_char,
    pub _IO_save_end: *mut libc::c_char,
    pub _markers: *mut _IO_marker,
    pub _chain: *mut _IO_FILE,
    pub _fileno: libc::c_int,
    pub _flags2: libc::c_int,
    pub _old_offset: __off_t,
    pub _cur_column: libc::c_ushort,
    pub _vtable_offset: libc::c_schar,
    pub _shortbuf: [libc::c_char; 1],
    pub _lock: *mut libc::c_void,
    pub _offset: __off64_t,
    pub __pad1: *mut libc::c_void,
    pub __pad2: *mut libc::c_void,
    pub __pad3: *mut libc::c_void,
    pub __pad4: *mut libc::c_void,
    pub __pad5: usize,
    pub _mode: libc::c_int,
    pub _unused2: [libc::c_char; 20],
}
type _IO_lock_t = ();
#[derive(Copy, Clone)]
#[repr(C)]
struct _IO_marker {
    pub _next: *mut _IO_marker,
    pub _sbuf: *mut _IO_FILE,
    pub _pos: libc::c_int,
}
type FILE = _IO_FILE;

#[derive(Clone)]
#[repr(C)]
struct lex {
    pub f: *mut FILE,
    pub next: Option<Token>,
}

impl lex {
    unsafe fn from_stdio(f: *mut FILE) -> Result<Self, LexError> {
        let mut ret = Self { f: f, next: None };

        ret.f = f;
        ret.next = Some(ret.next_tok()?);

        Ok(ret)
    }

    unsafe fn next_id_tok(&mut self) -> Result<Token, LexError> {
        let mut id_acc = vec![];

        loop {
            let mut peek = peekc(self.f);
            if peek == -1 && ferror(self.f) != 0 {
                return Err(LexError::IoError);
            }

            if *(*__ctype_b_loc()).offset(peek as isize) as libc::c_int
                & _ISalnum as libc::c_int as libc::c_ushort as libc::c_int
                == 0
            {
                break;
            }

            id_acc.push(nextc(self.f) as u8);
        }

        let id_str = String::from_utf8(id_acc).map_err(|e| LexError::InvalidUtf8 {
            cause: e.utf8_error(),
        })?;

        Ok(Token::Id(id_str))
    }

    unsafe fn next_num_tok(&mut self) -> Result<Token, LexError> {
        let mut val = 0u64;
        let mut dec_div = 1.0f64;
        let mut dec: bool = false;

        loop {
            let mut next = peekc(self.f);
            if next == -1 && ferror(self.f) != 0 {
                return Err(LexError::IoError);
            }
            if next as libc::c_int == '.' as i32 {
                if dec {
                    // Two dots in a numeric token
                    return Err(LexError::UnexpectedChar('.'));
                } else {
                    dec = 1 as libc::c_int != 0; // drop the dot
                    _IO_getc(self.f); // discard the number we've already
                }
            } else {
                if !(*(*__ctype_b_loc()).offset(next as libc::c_int as isize) as libc::c_int
                    & _ISdigit as libc::c_int as libc::c_ushort as libc::c_int
                    != 0)
                {
                    break;
                }
                _IO_getc(self.f);
                val = (10 as libc::c_int as libc::c_ulong)
                    .wrapping_mul(val)
                    .wrapping_add((next as libc::c_int - '0' as i32) as libc::c_ulong);
                if dec {
                    dec_div *= 10.0f64;
                }
            }
        }

        Ok(Token::Number(val as f64 / dec_div))
    }

    unsafe fn next_tok(&mut self) -> Result<Token, LexError> {
        let first = nextc(self.f) as libc::c_char;
        if first == -1 {
            if ferror(self.f) != 0 {
                return Err(LexError::IoError);
            }

            return Err(LexError::Eof);
        }

        Ok(match first as u8 as char {
            '/' => Token::Div,
            '-' => Token::Minus,
            '+' => Token::Plus,
            '*' => Token::Times,
            '\n' => Token::Newline,
            '(' => Token::OPar,
            ')' => Token::CPar,
            '^' => Token::Caret,
            ch => {
                ungetc(first as libc::c_int, self.f);

                if ch.is_ascii_digit() || ch == '.' {
                    self.next_num_tok()?
                } else if ch.is_ascii_alphabetic() {
                    self.next_id_tok()?
                } else {
                    return Err(LexError::UnexpectedChar(ch));
                }
            }
        })
    }

    pub unsafe fn next(&mut self) -> Result<Token, LexError> {
        if self.next.is_none() {
            return Err(LexError::Eof);
        }

        let some_succ = match self.next_tok() {
            Ok(tok) => Some(tok),
            Err(LexError::Eof) => None,
            Err(e) => return Err(e),
        };

        mem::replace(&mut self.next, some_succ).ok_or(LexError::Eof)
    }
}

impl Drop for lex {
    fn drop(&mut self) {
        unsafe {
            if self.f != stdin {
                fclose(self.f);
            }
        }
    }
}

type node_type = libc::c_uint;
const NODE_VAL: node_type = 8;
const NODE_TIMES: node_type = 7;
const NODE_POW: node_type = 6;
const NODE_PLUS: node_type = 5;
const NODE_NEG: node_type = 4;
const NODE_MINUS: node_type = 3;
const NODE_FUNC: node_type = 2;
const NODE_DIV: node_type = 1;
const NODE_CONST: node_type = 0;

#[derive(Copy, Clone)]
#[repr(C)]
struct node {
    pub kind: node_type,
    pub value: Value,
    pub left: *mut node,
    pub right: *mut node,
}

unsafe fn nextc(mut f: *mut FILE) -> libc::c_int {
    let mut ch: libc::c_char = 0;
    loop {
        ch = _IO_getc(f) as libc::c_char;
        if !(*(*__ctype_b_loc()).offset(ch as libc::c_int as isize) as libc::c_int
            & _ISblank as libc::c_int as libc::c_ushort as libc::c_int
            != 0)
        {
            break;
        }
    }
    return ch as libc::c_int;
}

unsafe fn peekc(mut f: *mut FILE) -> libc::c_int {
    let mut ret: libc::c_int = _IO_getc(f);
    if ret > 0 as libc::c_int {
        ungetc(ret, f);
    }
    return ret;
}

unsafe fn node_free(mut n: *mut node) {
    if !n.is_null() {
        node_free((*n).left);
        node_free((*n).right);
        dealloc(n as *mut u8, Layout::new::<node>());
    };
}

unsafe fn node_new(mut kind: node_type) -> *mut node {
    let mut ret: *mut node = alloc_zeroed(Layout::new::<node>()) as *mut node;
    (*ret).kind = kind;
    return ret;
}

unsafe fn node_bin_from_token(token: Token, left: *mut node, right: *mut node) -> *mut node {
    let mut ret: *mut node = alloc_zeroed(Layout::new::<node>()) as *mut node;

    use Token::*;
    match token {
        Caret => (*ret).kind = NODE_POW,
        Div => (*ret).kind = NODE_DIV,
        Minus => (*ret).kind = NODE_MINUS,
        Plus => (*ret).kind = NODE_PLUS,
        Times => (*ret).kind = NODE_TIMES,
        _ => {
            dealloc(ret as *mut u8, Layout::new::<node>());
            return ptr::null_mut();
        }
    }

    (*ret).left = left;
    (*ret).right = right;

    ret
}

unsafe fn parse_parens(lex: &mut lex) -> Result<*mut node, Error> {
    let par_expr = parse_expr(lex)?;

    let cpar_tok = match lex.next() {
        Ok(tok) => tok,
        Err(lerr) => {
            node_free(par_expr);
            return Err(lerr.into());
        }
    };

    if cpar_tok == Token::CPar {
        Ok(par_expr)
    } else {
        node_free(par_expr);

        Err(Error::expect(")", cpar_tok))
    }
}

unsafe fn parse_func(lex: &mut lex, mut id: *const libc::c_char) -> Result<*mut node, Error> {
    let c_id = CStr::from_ptr(id);

    let f_id = Func::try_from(c_id)?;

    // We know for sure lex->next is a parenthesis, therefore
    // parse_primary will slurp it, parse everything inside and slurp the
    // final ')'
    let mut call = parse_primary(lex)?;
    let mut ret: *mut node = node_new(NODE_FUNC);

    (*ret).value = Value::Func(f_id);
    (*ret).left = call;

    return Ok(ret);
}

unsafe fn parse_primary(lex: &mut lex) -> Result<*mut node, Error> {
    let ntok = lex.next().map_err(|lerr| {
        if lerr == LexError::Eof {
            parse_error!("unexpected EOF")
        } else {
            lerr.into()
        }
    })?;

    match ntok {
        Token::Id(id) => {
            let c_id = CString::new(id).unwrap();

            if lex.next == Some(Token::OPar) {
                return parse_func(lex, c_id.as_ptr());
            }

            let const_val = match Constant::try_from(c_id.as_ref()) {
                Ok(c) => c,
                Err(_) => {
                    return Err(parse_error!(
                        "unknown identifier '{}'",
                        c_id.to_str().unwrap(),
                    ));
                }
            };

            let num = node_new(NODE_CONST);
            (*num).value = Value::Constant(const_val);

            Ok(num)
        }
        Token::Number(n) => {
            let num_0 = node_new(NODE_VAL);

            (*num_0).value = Value::Number(n);

            Ok(num_0)
        }
        Token::OPar => parse_parens(lex),
        _ => Err(Error::expect("a number or parentheses", ntok)),
    }
}

unsafe fn parse_binary(
    lex: &mut lex,
    mut lhs: *mut node,
    mut min_prec: OpPrec,
) -> Result<*mut node, Error> {
    let mut cur_op_prec: OpPrec = 0;

    loop {
        let next = match &lex.next {
            Some(tok) => tok,
            None => break,
        };

        cur_op_prec = next.prec();

        if cur_op_prec >= min_prec && next.arity() == OpArity::Binary {
            let mut op_tok = lex.next()?;

            let mut rhs = parse_unary(lex)?;

            if let Some(next) = &lex.next {
                let next_op_prec = next.prec();
                let next_assoc_right = next.assoc() == OpAssoc::Right;

                if next_op_prec > cur_op_prec || next_assoc_right && next_op_prec == cur_op_prec {
                    rhs = parse_binary(lex, rhs, next_op_prec)?;
                }
            }

            lhs = node_bin_from_token(op_tok, lhs, rhs)
        } else {
            break;
        }
    }

    Ok(lhs)
}

unsafe fn parse_unary(lex: &mut lex) -> Result<*mut node, Error> {
    match &lex.next {
        Some(next) if next == &Token::Minus || next == &Token::Plus => {
            let op_top = lex.next()?;

            let right_expr = parse_unary(lex)?;

            if op_top == Token::Minus {
                if (*right_expr).kind as libc::c_uint != NODE_VAL as libc::c_int as libc::c_uint {
                    let mut neg_expr: *mut node = node_new(NODE_NEG);
                    (*neg_expr).left = right_expr;
                    return Ok(neg_expr);
                } else {
                    (*right_expr).value = Value::Number(
                        -f64::try_from((*right_expr).value)
                            .map_err(|_| parse_error!("cannot negate a non-number"))?,
                    );
                }
            }

            Ok(right_expr)
        }
        _ => parse_primary(lex),
    }
}

unsafe fn parse_expr(lex: &mut lex) -> Result<*mut node, Error> {
    if let Some(Token::Newline) | None = lex.next {
        return Ok(ptr::null_mut());
    }

    let mut lhs = parse_unary(lex)?;

    parse_binary(lex, lhs, -1i8)
}

unsafe fn node_dump_padded(mut node: *mut node, mut padding: u8, mut arrow: bool) {
    if node.is_null() {
        return;
    }
    let mut i: u8 = 0 as libc::c_int as u8;
    while (i as libc::c_int) < padding as libc::c_int {
        print!(" ");
        i = i.wrapping_add(1)
    }
    if arrow {
        // Sorry Windows, no fancy UTF-8 for you
        print!("└─→ ");
    }
    match (*node).kind as libc::c_uint {
        0 | 2 | 8 => {
            print!("{}", (*node).value);
        }
        1 => {
            print!("/");
        }
        3 => {
            print!("-");
        }
        4 => {
            print!("- (neg)");
        }
        5 => {
            print!("+");
        }
        6 => {
            print!("^");
        }
        7 => {
            print!("*");
        }
        _ => {}
    }
    print!("\n");
    node_dump_padded(
        (*node).left,
        (padding as libc::c_int + 2 as libc::c_int) as u8,
        1 as libc::c_int != 0,
    );
    node_dump_padded(
        (*node).right,
        (padding as libc::c_int + 2 as libc::c_int) as u8,
        1 as libc::c_int != 0,
    );
}

unsafe fn eval_node(mut node: *mut node) -> f64 {
    if node.is_null() {
        return f64::NAN;
    }

    let left: f64 = eval_node((*node).left);
    let right: f64 = eval_node((*node).right);
    match (*node).kind as libc::c_uint {
        0 | 2 | 8 => return (*node).value.eval(Some(left)),
        1 => return left / right,
        3 => return left - right,
        4 => return -left,
        5 => return left + right,
        6 => return left.powf(right),
        7 => return left * right,
        _ => {}
    }
    panic!("Reached end of non-void function without returning");
}

fn print_help(progname: &str) {
    eprint!("USAGE: {} [-t]\n\n", progname);
    eprintln!("A poor way to evaluate expressions");
}

fn main() {
    let mut print_node = false;
    let mut wants_help = false;
    let mut status = 0i32;

    let args: Vec<_> = std::env::args().collect();
    match args.len() {
        0 | 1 => {}
        2 => {
            match args[1].as_str() {
                "-t" => {
                    print_node = true;
                }
                "-h" => {
                    wants_help = true;
                }
                arg => {
                    eprintln!("error: unknown parameter '{}'\n", arg);
                    wants_help = true;
                    status = -1;
                }
            };
        }
        _ => {
            eprintln!("error: too many arguments\n");
            status = -1;
            wants_help = true;
        }
    }

    if wants_help {
        print_help(&args[0]);
        exit(status);
    }

    unsafe {
        let mut lex = match lex::from_stdio(stdin) {
            Ok(lex) => lex,
            Err(lerr) => {
                eprintln!("error: {}", lerr);

                exit(1i32);
            }
        };

        loop {
            match parse_expr(&mut lex) {
                Ok(tree) => {
                    let res: f64 = eval_node(tree);
                    // eval_node(NULL) (i.e. empty expression) always returns NaN.
                    // Avoid printing it (it's probably because someone has typed ctrl+d)
                    if !tree.is_null() {
                        if print_node {
                            println!("\nTree:\n");
                            node_dump_padded(tree, 0u8, false);
                            println!("");
                        }

                        println!("{}", GPoint(res));
                    }
                    node_free(tree);

                    match lex.next() {
                        Ok(ntok) => {
                            if ntok != Token::Newline {
                                eprintln!(
                                    "error: stray '{}' left in stream after expression",
                                    ntok,
                                );

                                status = 1i32;
                                break;
                            } else {
                                status = 0 as libc::c_int
                            }
                        }

                        Err(LexError::Eof) => {
                            break;
                        }

                        Err(lerr) => {
                            eprintln!("error: {}", lerr);

                            status = 1i32;
                            break;
                        }
                    }
                }
                Err(err) => {
                    eprintln!("error: {}", err);
                    status = 1i32;

                    break;
                }
            }
        }
    }

    exit(status);
}
