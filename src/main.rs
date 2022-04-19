#![feature(c_variadic)]
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
    error,
    ffi::{CStr, CString},
    fmt,
    process::exit,
    ptr,
};

use gpoint::GPoint;

#[derive(Eq, Debug, PartialEq)]
enum LexError {
    Eof,
    IdTooLong,
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
        None
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LexError::Eof => write!(f, "reached end of file"),
            LexError::IdTooLong => write!(f, "identifier too long"),
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TokenKind {
    Div,
    Minus,
    Number,
    Plus,
    Times,
    Newline,
    OPar,
    CPar,
    Caret,
    Id,
}

impl TokenKind {
    const fn arity(self) -> OpArity {
        use TokenKind::*;

        match self {
            Div | Minus | Plus | Times | Caret => OpArity::Binary,
            Number | Newline | OPar | CPar | Id => OpArity::None,
        }
    }

    const fn assoc(self) -> OpAssoc {
        use TokenKind::*;

        match self {
            Div | Minus | Plus | Times => OpAssoc::Left,
            Number | Newline | OPar | CPar | Id => OpAssoc::None,
            Caret => OpAssoc::Right,
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenKind::*;

        match self {
            Div => write!(f, "/"),
            Minus => write!(f, "-"),
            Number => write!(f, "<number>"),
            Plus => write!(f, "+"),
            Times => write!(f, "*"),
            Newline => write!(f, "\\n"),
            OPar => write!(f, "("),
            CPar => write!(f, ")"),
            Caret => write!(f, "^"),
            Id => write!(f, "<id>"),
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

    static mut stderr: *mut _IO_FILE;

    fn fclose(__stream: *mut FILE) -> libc::c_int;

    fn fprintf(_: *mut FILE, _: *const libc::c_char, _: ...) -> libc::c_int;

    fn printf(_: *const libc::c_char, _: ...) -> libc::c_int;

    fn vasprintf(
        __ptr: *mut *mut libc::c_char,
        __f: *const libc::c_char,
        __arg: ::std::ffi::VaList,
    ) -> libc::c_int;

    fn putchar(__c: libc::c_int) -> libc::c_int;

    fn ferror(__stream: *mut FILE) -> libc::c_int;

    fn fputs(__s: *const libc::c_char, __stream: *mut FILE) -> libc::c_int;

    fn puts(__s: *const libc::c_char) -> libc::c_int;

    fn ungetc(__c: libc::c_int, __stream: *mut FILE) -> libc::c_int;

    fn calloc(_: libc::c_ulong, _: libc::c_ulong) -> *mut libc::c_void;

    fn free(__ptr: *mut libc::c_void);

    fn memset(_: *mut libc::c_void, _: libc::c_int, _: libc::c_ulong) -> *mut libc::c_void;

    fn strcmp(_: *const libc::c_char, _: *const libc::c_char) -> libc::c_int;
}
type __builtin_va_list = [__va_list_tag; 1];
#[derive(Copy, Clone)]
#[repr(C)]
struct __va_list_tag {
    pub gp_offset: libc::c_uint,
    pub fp_offset: libc::c_uint,
    pub overflow_arg_area: *mut libc::c_void,
    pub reg_save_area: *mut libc::c_void,
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
type va_list = __builtin_va_list;
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

#[derive(Copy, Clone)]
#[repr(C)]
struct tok {
    pub kind: TokenKind,
    pub c2rust_unnamed: C2RustUnnamed_0,
}

#[derive(Copy, Clone)]
#[repr(C)]
union C2RustUnnamed_0 {
    pub num_val: f64,
    pub id: [libc::c_char; 8],
}

#[derive(Copy, Clone)]
#[repr(C)]
struct lex {
    pub f: *mut FILE,
    pub next: *mut tok,
    pub eof: bool,
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
#[derive(Copy, Clone)]
#[repr(C)]
struct parse_res {
    pub ok: bool,
    pub c2rust_unnamed: C2RustUnnamed_2,
}

#[derive(Copy, Clone)]
#[repr(C)]
union C2RustUnnamed_2 {
    pub tree: *mut node,
    pub error: *mut libc::c_char,
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

static mut OP_PREC: [OpPrec; 10] = [
    2 as libc::c_int as OpPrec,
    1 as libc::c_int as OpPrec,
    -(1 as libc::c_int) as OpPrec,
    1 as libc::c_int as OpPrec,
    2 as libc::c_int as OpPrec,
    -(1 as libc::c_int) as OpPrec,
    -(1 as libc::c_int) as OpPrec,
    -(1 as libc::c_int) as OpPrec,
    3 as libc::c_int as OpPrec,
    -(1 as libc::c_int) as OpPrec,
];

// kind == ID

unsafe fn tok_dump(mut tok: tok) {
    match tok.kind {
        TokenKind::Number => {
            printf(
                b"%g\x00" as *const u8 as *const libc::c_char,
                tok.c2rust_unnamed.num_val,
            );
        }
        TokenKind::Id => {
            fputs(tok.c2rust_unnamed.id.as_mut_ptr(), stdout);
        }
        _ => print!("{}", tok.kind),
    }; // preload first token
}

unsafe fn lex_init(mut lex: *mut lex, mut f: *mut FILE) -> Result<LexState, LexError> {
    (*lex).f = f;
    (*lex).eof = 0 as libc::c_int != 0;
    (*lex).next = calloc(
        1 as libc::c_int as libc::c_ulong,
        ::std::mem::size_of::<tok>() as libc::c_ulong,
    ) as *mut tok;
    return lex_next_tok(lex);
}

unsafe fn lex_invalid(mut lex: *mut lex) {
    free((*lex).next as *mut libc::c_void);
    (*lex).next = 0 as *mut tok;
}

unsafe fn lex_deinit(mut lex: *mut lex) {
    lex_invalid(lex);
    if (*lex).f != stdin {
        fclose((*lex).f);
    };
}

unsafe fn lex_next_id_tok(mut lex: *mut lex) -> Result<LexState, LexError> {
    let max_id_sz = ::std::mem::size_of::<[libc::c_char; 8]>() as libc::c_ulong;
    memset(
        (*(*lex).next).c2rust_unnamed.id.as_mut_ptr() as *mut libc::c_void,
        0 as libc::c_int,
        max_id_sz,
    );
    let mut i = 0;
    while i < max_id_sz.wrapping_sub(1 as libc::c_int as libc::c_ulong) {
        let mut peek: libc::c_char = peekc((*lex).f) as libc::c_char;
        if peek as libc::c_int == -(1 as libc::c_int) && ferror((*lex).f) != 0 {
            return Err(LexError::IoError);
        }
        if *(*__ctype_b_loc()).offset(peek as libc::c_int as isize) as libc::c_int
            & _ISalnum as libc::c_int as libc::c_ushort as libc::c_int
            == 0
        {
            break;
        }
        (*(*lex).next).c2rust_unnamed.id[i as usize] = nextc((*lex).f) as libc::c_char;
        i = i.wrapping_add(1)
    }
    // Only true when we exited the loop because we got more
    // chars than we could store (and there are still alphanumeric
    // on the stream)
    if *(*__ctype_b_loc()).offset(peekc((*lex).f) as isize) as libc::c_int
        & _ISalnum as libc::c_int as libc::c_ushort as libc::c_int
        != 0
    {
        return Err(LexError::IdTooLong);
    }

    (*(*lex).next).kind = TokenKind::Id;

    return Ok(LexState::Ok);
}

unsafe fn lex_next_num_tok(mut lex: *mut lex) -> Result<LexState, LexError> {
    let mut val: u64 = 0 as libc::c_int as u64;
    let mut dec_div: f64 = 1.0f64;
    let mut dec: bool = 0 as libc::c_int != 0;
    loop {
        let mut next: libc::c_char = peekc((*lex).f) as libc::c_char;
        if next as libc::c_int == -(1 as libc::c_int) && ferror((*lex).f) != 0 {
            return Err(LexError::IoError);
        }
        if next as libc::c_int == '.' as i32 {
            if dec {
                // Two dots in a numeric token
                return Err(LexError::UnexpectedChar('.'));
            } else {
                dec = 1 as libc::c_int != 0; // drop the dot
                _IO_getc((*lex).f); // discard the number we've already
            }
        } else {
            if !(*(*__ctype_b_loc()).offset(next as libc::c_int as isize) as libc::c_int
                & _ISdigit as libc::c_int as libc::c_ushort as libc::c_int
                != 0)
            {
                break;
            }
            _IO_getc((*lex).f);
            val = (10 as libc::c_int as libc::c_ulong)
                .wrapping_mul(val)
                .wrapping_add((next as libc::c_int - '0' as i32) as libc::c_ulong);
            if dec {
                dec_div *= 10 as libc::c_int as f64
            }
        }
    }
    *(*lex).next = {
        let mut init = tok {
            kind: TokenKind::Number,
            c2rust_unnamed: C2RustUnnamed_0 {
                num_val: val as f64 / dec_div,
            },
        };
        init
    };
    return Ok(LexState::Ok);
}

unsafe fn lex_next_tok(mut lex: *mut lex) -> Result<LexState, LexError> {
    let first = nextc((*lex).f) as libc::c_char;
    if first == -1 {
        if ferror((*lex).f) != 0 {
            return Err(LexError::IoError);
        }

        return Err(LexError::Eof);
    }

    match first as u8 as char {
        '/' => (*(*lex).next).kind = TokenKind::Div,
        '-' => (*(*lex).next).kind = TokenKind::Minus,
        '+' => (*(*lex).next).kind = TokenKind::Plus,
        '*' => (*(*lex).next).kind = TokenKind::Times,
        '\n' => (*(*lex).next).kind = TokenKind::Newline,
        '(' => (*(*lex).next).kind = TokenKind::OPar,
        ')' => (*(*lex).next).kind = TokenKind::CPar,
        '^' => (*(*lex).next).kind = TokenKind::Caret,
        ch => {
            ungetc(first  as libc::c_int, (*lex).f);
            if ch.is_ascii_digit() || ch == '.' {
                return lex_next_num_tok(lex);
            } else if ch.is_ascii_alphabetic() {
                return lex_next_id_tok(lex);
            } else {
                return Err(LexError::UnexpectedChar(ch));
            }
        }
    }

    return Ok(LexState::Ok);
}

unsafe fn lex_next(mut lex: *mut lex, mut res_tok: *mut tok) -> Result<LexState, LexError> {
    if (*lex).eof {
        return Err(LexError::Eof);
    }

    if !res_tok.is_null() {
        *res_tok = *(*lex).next
    }

    let res = lex_next_tok(lex);    
    
    match &res {
        Err(LexError::Eof) => {
            (*lex).eof = true;
        }
        Err(_) => {
            lex_invalid(lex);
        }
        Ok(_) => {},
    };

    res
}

unsafe fn node_free(mut n: *mut node) {
    if !n.is_null() {
        node_free((*n).left);
        node_free((*n).right);
        free(n as *mut libc::c_void);
    };
}

unsafe fn node_new(mut kind: node_type) -> *mut node {
    let mut ret: *mut node = calloc(
        1 as libc::c_int as libc::c_ulong,
        ::std::mem::size_of::<node>() as libc::c_ulong,
    ) as *mut node;
    (*ret).kind = kind;
    return ret;
}

unsafe fn node_bin_from_token(
    mut kind: TokenKind,
    mut left: *mut node,
    mut right: *mut node,
) -> *mut node {
    let mut ret: *mut node = calloc(
        1 as libc::c_int as libc::c_ulong,
        ::std::mem::size_of::<node>() as libc::c_ulong,
    ) as *mut node;
    match kind as libc::c_uint {
        8 => (*ret).kind = NODE_POW,
        0 => (*ret).kind = NODE_DIV,
        1 => (*ret).kind = NODE_MINUS,
        3 => (*ret).kind = NODE_PLUS,
        4 => (*ret).kind = NODE_TIMES,
        _ => {
            free(ret as *mut libc::c_void);
            return 0 as *mut node;
        }
    }
    (*ret).left = left;
    (*ret).right = right;
    return ret;
}

static mut RES_EMPTY: parse_res = {
    let mut init = parse_res {
        ok: 1 as libc::c_int != 0,
        c2rust_unnamed: C2RustUnnamed_2 {
            tree: 0 as *const node as *mut node,
        },
    };
    init
};

unsafe fn pres_get_err(mut res: parse_res) -> *mut libc::c_char {
    return if res.ok as libc::c_int != 0 {
        0 as *mut libc::c_char
    } else {
        res.c2rust_unnamed.error
    };
}

unsafe fn pres_get_tree(mut res: parse_res) -> *mut node {
    return if res.ok as libc::c_int != 0 {
        res.c2rust_unnamed.tree
    } else {
        0 as *mut node
    };
}

unsafe extern "C" fn pres_err(fmt: *const libc::c_char, mut args: ...) -> parse_res {
    let mut args_0: ::std::ffi::VaListImpl;
    args_0 = args.clone();
    let mut ret: parse_res = {
        let mut init = parse_res {
            ok: 0 as libc::c_int != 0,
            c2rust_unnamed: C2RustUnnamed_2 {
                tree: 0 as *mut node,
            },
        };
        init
    };
    vasprintf(&mut ret.c2rust_unnamed.error, fmt, args_0.as_va_list());
    return ret;
}

unsafe fn pres_expect(mut expect: *const libc::c_char, mut got: TokenKind) -> parse_res {
    let cstr = CString::new(got.to_string()).unwrap();

    return pres_err(
        b"expecting %s, got \'%s\'\x00" as *const u8 as *const libc::c_char,
        expect,
        cstr.as_ptr(),
    );
}

unsafe fn pres_lex_err(mut lerr: LexError) -> parse_res {
    let cstr = lerr.to_cstring();

    return pres_err(
        b"%s\x00" as *const u8 as *const libc::c_char,
        cstr.as_ptr(),
    );
}

unsafe fn pres_ok(mut tree: *mut node) -> parse_res {
    return {
        let mut init = parse_res {
            ok: 1 as libc::c_int != 0,
            c2rust_unnamed: C2RustUnnamed_2 { tree: tree },
        };
        init
    };
}

unsafe fn parse_parens(mut lex: *mut lex) -> parse_res {
    let mut par_expr_res: parse_res = parse_expr(lex);
    if !par_expr_res.ok {
        return par_expr_res;
    }
    let mut par_expr: *mut node = pres_get_tree(par_expr_res);
    let mut cpar_tok: tok = tok {
        kind: TokenKind::Div,
        c2rust_unnamed: C2RustUnnamed_0 { num_val: 0. },
    };
    let mut lres = lex_next(lex, &mut cpar_tok);
    if let Err(lerr) = lres {
        node_free(par_expr);
        return pres_lex_err(lerr);
    }
    if cpar_tok.kind as libc::c_uint != TokenKind::CPar as libc::c_int as libc::c_uint {
        node_free(par_expr);
        return pres_expect(
            b"\')\'\x00" as *const u8 as *const libc::c_char,
            cpar_tok.kind,
        );
    }
    return pres_ok(par_expr);
}

unsafe fn parse_func(mut lex: *mut lex, mut id: *const libc::c_char) -> parse_res {
    let c_id = CStr::from_ptr(id);

    let mut f_id = match Func::try_from(c_id) {
        Ok(f) => f,
        Err(_) => {
            return pres_err(
                b"unknown function \'%s\'\x00" as *const u8 as *const libc::c_char,
                id,
            )
        }
    };

    // We know for sure lex->next is a parenthesis, therefore
    // parse_primary will slurp it, parse everything inside and slurp the
    // final ')'
    let mut call_res: parse_res = parse_primary(lex);
    if !call_res.ok {
        return call_res;
    }
    let mut call: *mut node = pres_get_tree(call_res);
    let mut ret: *mut node = node_new(NODE_FUNC);
    (*ret).value = Value::Func(f_id);
    (*ret).left = call;
    return pres_ok(ret);
}

unsafe fn parse_primary(mut lex: *mut lex) -> parse_res {
    let mut ntok: tok = tok {
        kind: TokenKind::Div,
        c2rust_unnamed: C2RustUnnamed_0 { num_val: 0. },
    };

    let mut lres = lex_next(lex, &mut ntok);

    if let Err(lerr) = lres {
        return if lerr == LexError::Eof {
            pres_err(b"unexpected EOF\x00" as *const u8 as *const libc::c_char)
        } else {
            return pres_lex_err(lerr);
        }
    }

    match ntok.kind as libc::c_uint {
        9 => {
            if !(*lex).next.is_null()
                && (*(*lex).next).kind as libc::c_uint
                    == TokenKind::OPar as libc::c_int as libc::c_uint
            {
                return parse_func(lex, ntok.c2rust_unnamed.id.as_mut_ptr());
            }

            let c_id = CStr::from_ptr(ntok.c2rust_unnamed.id.as_ptr());
            let const_val = match Constant::try_from(c_id) {
                Ok(c) => c,
                Err(_) => {
                    return pres_err(
                        b"unknown identifier '%s'\x00" as *const u8 as *const libc::c_char,
                        c_id.as_ptr(),
                    )
                }
            };

            let mut num: *mut node = node_new(NODE_CONST);
            (*num).value = Value::Constant(const_val);
            return pres_ok(num);
        }
        2 => {
            let mut num_0: *mut node = node_new(NODE_VAL);
            (*num_0).value = Value::Number(ntok.c2rust_unnamed.num_val);
            return pres_ok(num_0);
        }
        6 => return parse_parens(lex),
        _ => {
            return pres_expect(
                b"a number or parentheses\x00" as *const u8 as *const libc::c_char,
                ntok.kind,
            )
        }
    };
}

unsafe fn parse_binary(lex: *mut lex, mut lhs: *mut node, mut min_prec: OpPrec) -> parse_res {
    let mut cur_op_prec: OpPrec = 0;
    let mut rhs: *mut node = 0 as *mut node;
    while !(*lex).next.is_null()
        && {
            cur_op_prec = OP_PREC[(*(*lex).next).kind as usize];
            (cur_op_prec as libc::c_int) >= min_prec as libc::c_int
        }
        && (*(*lex).next).kind.arity() == OpArity::Binary
    {
        let mut op_tok: tok = tok {
            kind: TokenKind::Div,
            c2rust_unnamed: C2RustUnnamed_0 { num_val: 0. },
        };

        if let Err(lerr) = lex_next(lex, &mut op_tok) {
            return pres_lex_err(lerr);
        }

        let mut rhs_res: parse_res = parse_unary(lex);
        if !rhs_res.ok {
            return rhs_res;
        }
        rhs = pres_get_tree(rhs_res);
        if !(*lex).next.is_null() {
            let next_op_prec: OpPrec = OP_PREC[(*(*lex).next).kind as usize];
            let next_assoc_right = (*(*lex).next).kind.assoc() == OpAssoc::Right;
            if next_op_prec as libc::c_int > cur_op_prec as libc::c_int
                || next_assoc_right as libc::c_int != 0
                    && next_op_prec as libc::c_int == cur_op_prec as libc::c_int
            {
                rhs_res = parse_binary(lex, rhs, next_op_prec);
                if !rhs_res.ok {
                    return rhs_res;
                }
                rhs = pres_get_tree(rhs_res)
            }
        }
        lhs = node_bin_from_token(op_tok.kind, lhs, rhs)
    }
    return pres_ok(lhs);
}

unsafe fn parse_unary(lex: *mut lex) -> parse_res {
    if !(*lex).next.is_null()
        && ((*(*lex).next).kind as libc::c_uint == TokenKind::Minus as libc::c_int as libc::c_uint
            || (*(*lex).next).kind as libc::c_uint
                == TokenKind::Plus as libc::c_int as libc::c_uint)
    {
        let mut op_top: tok = tok {
            kind: TokenKind::Div,
            c2rust_unnamed: C2RustUnnamed_0 { num_val: 0. },
        };
        
        if let Err(lerr) = lex_next(lex, &mut op_top) {
            return pres_lex_err(lerr);
        }

        let mut right_expr_res: parse_res = parse_unary(lex);
        if !right_expr_res.ok {
            return right_expr_res;
        }
        let mut right_expr: *mut node = pres_get_tree(right_expr_res);
        if op_top.kind as libc::c_uint == TokenKind::Minus as libc::c_int as libc::c_uint {
            if (*right_expr).kind as libc::c_uint != NODE_VAL as libc::c_int as libc::c_uint {
                let mut neg_expr: *mut node = node_new(NODE_NEG);
                (*neg_expr).left = right_expr;
                return pres_ok(neg_expr);
            } else {
                match f64::try_from((*right_expr).value) {
                    Ok(val) => (*right_expr).value = Value::Number(-val),
                    Err(_) => {
                        return pres_err(
                            b"cannot negate non-numeric value\x00" as *const u8
                                as *const libc::c_char,
                        )
                    }
                }
            }
        }
        return pres_ok(right_expr);
    } else {
        return parse_primary(lex);
    };
}

unsafe fn parse_expr(lex: *mut lex) -> parse_res {
    if (*lex).next.is_null()
        || (*(*lex).next).kind as libc::c_uint == TokenKind::Newline as libc::c_int as libc::c_uint
    {
        return RES_EMPTY;
    }
    let mut res: parse_res = parse_unary(lex);
    if !pres_get_err(res).is_null() {
        return res;
    }
    let mut lhs: *mut node = pres_get_tree(res);
    return parse_binary(lex, lhs, -(1 as libc::c_int) as OpPrec);
}

unsafe fn node_dump_padded(mut node: *mut node, mut padding: u8, mut arrow: bool) {
    if node.is_null() {
        return;
    }
    let mut i: u8 = 0 as libc::c_int as u8;
    while (i as libc::c_int) < padding as libc::c_int {
        putchar(' ' as i32);
        i = i.wrapping_add(1)
    }
    if arrow {
        // Sorry Windows, no fancy UTF-8 for you
        fputs(
            b"\xe2\x94\x94\xe2\x94\x80\xe2\x86\x92 \x00" as *const u8 as *const libc::c_char,
            stdout,
        );
    }
    match (*node).kind as libc::c_uint {
        0 | 2 | 8 => {
            fputs((*node).value.to_cstring().as_ptr(), stdout);
        }
        1 => {
            putchar('/' as i32);
        }
        3 => {
            putchar('-' as i32);
        }
        4 => {
            fputs(b"- (neg)\x00" as *const u8 as *const libc::c_char, stdout);
        }
        5 => {
            putchar('+' as i32);
        }
        6 => {
            putchar('^' as i32);
        }
        7 => {
            putchar('*' as i32);
        }
        _ => {}
    }
    putchar('\n' as i32);
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

    let mut lex = lex {
        f: ptr::null_mut(),
        next: ptr::null_mut(),
        eof: false,
    };

    unsafe {
        if let Err(lerr) =  lex_init(&mut lex, stdin) {
            eprintln!("error: {}", lerr);

            exit(1i32);
        }

        loop {
            let pres: parse_res = parse_expr(&mut lex);
            if pres.ok {
                let tree: *mut node = pres_get_tree(pres);
                let res: f64 = eval_node(tree);
                // eval_node(NULL) (i.e. empty expression) always returns NaN.
                // Avoid printing it (it's probably because someone has typed ctrl+d)
                if !tree.is_null() {
                    if print_node {
                        println!("\nTree:\n");
                        node_dump_padded(tree, 0 as libc::c_int as u8, 0 as libc::c_int != 0);
                        println!("");
                    }

                    println!("{}", GPoint(res));
                }
                node_free(tree);
                let mut ntok: tok = tok {
                    kind: TokenKind::Div,
                    c2rust_unnamed: C2RustUnnamed_0 { num_val: 0. },
                };

                match lex_next(&mut lex, &mut ntok) {
                    Ok(_) => {
                        if ntok.kind != TokenKind::Newline {
                            eprintln!(
                                "error: stray '{}' left in stream after expression",
                                ntok.kind as usize,
                            );

                            status = 1 as libc::c_int;
                            break;
                        } else {
                            status = 0 as libc::c_int
                        }
                    },

                    Err(LexError::Eof) => {
                        break;
                    },

                    Err(lerr) => {
                        eprintln!("error: {}", lerr);

                        status = 1i32
                    }
                }
            } else {
                let mut err: *mut libc::c_char = pres_get_err(pres);
                fprintf(
                    stderr,
                    b"error: %s\n\x00" as *const u8 as *const libc::c_char,
                    err,
                );
                free(err as *mut libc::c_void);
                status = 1i32
            }
        }
        lex_deinit(&mut lex);
    }

    exit(status);
}
