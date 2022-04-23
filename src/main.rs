#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
)]

use std::{
    error,
    ffi::{CStr, CString},
    fmt, io, mem,
    process::exit,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BinaryOp {
    Div,
    Plus,
    Pow,
    Minus,
    Times,
}

impl TryFrom<Token> for BinaryOp {
    type Error = Error;

    fn try_from(token: Token) -> Result<Self, Self::Error> {
        match token {
            Token::Caret => Ok(BinaryOp::Pow),
            Token::Div => Ok(BinaryOp::Div),
            Token::Plus => Ok(BinaryOp::Plus),
            Token::Minus => Ok(BinaryOp::Minus),
            Token::Times => Ok(BinaryOp::Times),
            _ => Err(Error::expect("binary operator", token)),
        }
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use BinaryOp::*;

        match self {
            Div => write!(f, "/"),
            Plus => write!(f, "+"),
            Pow => write!(f, "^"),
            Minus => write!(f, "-"),
            Times => write!(f, "*"),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
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

#[derive(Clone, Debug, PartialEq)]
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
        expr: Box<Node>,
    },
    Value(Value),
}

impl Node {
    pub fn dump(&self) {
        self.dump_to(&mut io::stdout()).unwrap();
    }

    pub fn dump_to(&self, w: &mut impl io::Write) -> Result<(), io::Error> {
        self.dump_tree_impl_to(w, 0, false)
    }

    fn dump_tree_impl_to(
        &self,
        w: &mut impl io::Write,
        padding: u8,
        arrow: bool,
    ) -> Result<(), io::Error> {
        for _ in 0..padding {
            write!(w, " ")?;
        }

        if arrow {
            write!(w, "└─→ ")?;
        }

        use Node::*;

        match self {
            Binary { op, lhs, rhs } => {
                writeln!(w, "{}", op)?;

                lhs.dump_tree_impl_to(w, padding + 2, true)?;
                rhs.dump_tree_impl_to(w, padding + 2, true)?;
            }
            Call { func, args } => {
                writeln!(w, "{}", func)?;

                args.first().unwrap().dump_tree_impl_to(w, padding + 2, true)?;
            }
            Unary { op, expr: arg } => {
                writeln!(w, "{}", op)?;

                arg.dump_tree_impl_to(w, padding + 2, true)?;
            }
            Value(val) => {
                writeln!(w, "{}", val)?;
            }
        };

        Ok(())
    }

    fn eval(&self) -> f64 {
        use Node::*;
    
        match self {
            Binary { op, lhs, rhs } => {
                let left = lhs.eval();
                let right = rhs.eval();
    
                use BinaryOp::*;
    
                match op {
                    Div => left / right,
                    Minus => left - right,
                    Pow => left.powf(right),
                    Plus => left + right,
                    Times => left * right,
                }
            },
            Call { func, args } => {
                let arg = args.first().expect("no args").eval();
    
                func.eval(arg)
            }
            Value(val) => val.into(),
            Unary { op, expr } => {
                let right = expr.eval();
    
                use UnaryOp::*;
    
                match op {
                    Neg => -right,
                }
            }
        }
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Node::*;

        match self {
            Binary { op, lhs, rhs } => write!(f, "{} {} {}", lhs, op, rhs),
            Call { func, args } => write!(
                f,
                "{}({})",
                func,
                args.iter()
                    .map(|n| format!("{}", n))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Unary { op, expr: arg } => write!(f, "{}{}", op, arg),
            Value(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum OpArity {
    Binary,
    None,
    Unary,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum OpAssoc {
    Left,
    None,
    Right,
}

type OpPrec = i8;

#[derive(Clone, Debug, PartialEq)]
enum Token {
    Caret,
    CPar,
    Div,
    Id(String),
    Minus,
    Newline,
    Number(f64),
    OPar,
    Plus,
    Times,
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
            Caret => 3,
            Div => 2,
            Minus => 1,
            Plus => 1,
            Times => 2,
            _ => -1,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Token::*;

        match self {
            Caret => write!(f, "^"),
            CPar => write!(f, ")"),
            Div => write!(f, "/"),
            Id(str) => write!(f, "{}", str),
            Minus => write!(f, "-"),
            Newline => write!(f, "\\n"),
            Number(n) => write!(f, "{}", GPoint(*n)),
            Plus => write!(f, "+"),
            OPar => write!(f, "("),
            Times => write!(f, "*"),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum UnaryOp {
    Neg,
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use UnaryOp::*;

        match self {
            Neg => write!(f, "-"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Value {
    Constant(Constant),
    Number(f64),
}

impl From<&Value> for f64 {
    fn from(v: &Value) -> Self {
        match v {
            Value::Constant(c) => Self::from(*c),
            Value::Number(n) => *n,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Value::*;

        match *self {
            Constant(c) => write!(f, "{}", c),
            Number(n) => write!(f, "{}", GPoint(n)),
        }
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
    fn from_stdio(f: *mut FILE) -> Result<Self, LexError> {
        let mut ret = Self { f: f, next: None };

        ret.f = f;
        ret.next = unsafe {
            Some(ret.next_tok()?)
        };

        Ok(ret)
    }

    unsafe fn next_id_tok(&mut self) -> Result<Token, LexError> {
        let mut id_acc = vec![];

        loop {
            let peek = peekc(self.f);
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
            let next = peekc(self.f);
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

    pub fn next(&mut self) -> Result<Token, LexError> {
        if self.next.is_none() {
            return Err(LexError::Eof);
        }

        unsafe {
            let some_succ = match self.next_tok() {
                Ok(tok) => Some(tok),
                Err(LexError::Eof) => None,
                Err(e) => return Err(e),
            };

            mem::replace(&mut self.next, some_succ).ok_or(LexError::Eof)
        }
    }

    pub fn try_discard(&mut self) -> bool {
        self.next().is_ok()
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

unsafe fn nextc(f: *mut FILE) -> libc::c_int {
    loop {
        let ch = _IO_getc(f) as libc::c_char;
        if !(*(*__ctype_b_loc()).offset(ch as libc::c_int as isize) as libc::c_int
            & _ISblank as libc::c_int as libc::c_ushort as libc::c_int
            != 0)
        {
            return ch as libc::c_int;
        }
    }
}

unsafe fn peekc(f: *mut FILE) -> libc::c_int {
    let ret = _IO_getc(f);

    if ret > 0 as libc::c_int {
        ungetc(ret, f);
    }
    
    return ret;
}

fn parse_parens(lex: &mut lex) -> Result<Node, Error> {
    let par_expr = parse_expr(lex)?;

    let cpar_tok = lex.next()?;

    if cpar_tok == Token::CPar {
        Ok(par_expr)
    } else {
        Err(Error::expect(")", cpar_tok))
    }
}

fn parse_func(lex: &mut lex, id: &str) -> Result<Node, Error> {
    let f_id = Func::try_from(id)?;

    // We know for sure lex->next is a parenthesis, therefore
    // parse_primary will slurp it, parse everything inside and slurp the
    // final ')'
    let call = parse_primary(lex)?;

    Ok(Node::Call {
        func: f_id,
        args: vec![call],
    })
}

fn parse_primary(lex: &mut lex) -> Result<Node, Error> {
    let ntok = lex.next().map_err(|lerr| {
        if lerr == LexError::Eof {
            parse_error!("unexpected EOF")
        } else {
            lerr.into()
        }
    })?;

    match ntok {
        Token::Id(ref id) => {
            if lex.next == Some(Token::OPar) {
                return parse_func(lex, id);
            }

            let const_val = match Constant::try_from(&id as &str) {
                Ok(c) => c,
                Err(_) => {
                    return Err(parse_error!(
                        "unknown identifier '{}'",
                        id,
                    ));
                }
            };

            let value = Value::Constant(const_val);

            Ok(Node::Value(value))
        }
        Token::Number(n) => {
            let value = Value::Number(n);

            Ok(Node::Value(value))
        }
        Token::OPar => parse_parens(lex),
        _ => Err(Error::expect("a number or parentheses", ntok)),
    }
}

fn parse_binary(
    lex: &mut lex,
    mut lhs: Node,
    min_prec: OpPrec,
) -> Result<Node, Error> {
    let mut cur_op_prec: OpPrec;

    loop {
        let next = match &lex.next {
            Some(tok) => tok,
            None => break,
        };

        cur_op_prec = next.prec();

        if cur_op_prec >= min_prec && next.arity() == OpArity::Binary {
            let op_tok = lex.next()?;

            let mut rhs = parse_unary(lex)?;

            if let Some(next) = &lex.next {
                let next_op_prec = next.prec();
                let next_assoc_right = next.assoc() == OpAssoc::Right;

                if next_op_prec > cur_op_prec || next_assoc_right && next_op_prec == cur_op_prec {
                    rhs = parse_binary(lex, rhs, next_op_prec)?;
                }
            }

            lhs = Node::Binary{ 
                op: op_tok.try_into()?,
                lhs: lhs.into(),
                rhs: rhs.into(),
            };
        } else {
            break;
        }
    }

    Ok(lhs)
}

fn parse_unary(lex: &mut lex) -> Result<Node, Error> {
    match &lex.next {
        Some(next) if next == &Token::Minus || next == &Token::Plus => {
            let op_top = lex.next()?;

            let right_expr = parse_unary(lex)?;

            match op_top {
                Token::Minus => Ok(
                    if let Node::Value(Value::Number(num)) = right_expr {                        
                        let new_val = Value::Number(-num);

                        Node::Value(new_val)
                    } else {
                        Node::Unary {
                            op: UnaryOp::Neg,
                            expr: right_expr.into(),
                        }
                    }
                ),
                Token::Plus => Ok(right_expr),
                _ => unreachable!(),
            }
        }
        _ => parse_primary(lex),
    }
}

fn parse_expr(lex: &mut lex) -> Result<Node, Error> {
    let lhs = parse_unary(lex)?;
    
    parse_binary(lex, lhs, -1i8)
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
            if lex.next.is_none() {
                break;
            }

            if let Some(Token::Newline) = &lex.next {
                // Discard the newline
                lex.try_discard();
            }

            match parse_expr(&mut lex) {
                Ok(tree) => {
                    let res: f64 = tree.eval();

                    if print_node {
                        println!("\nTree:\n");
                        tree.dump();
                        println!("");
                    }

                    println!("{}", GPoint(res));

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
