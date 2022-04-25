use std::{error, ffi::CStr, fmt, io, iter::Peekable, process::exit};

use gpoint::GPoint;

#[macro_use]
mod macros;

mod charsource;

use charsource::{Chars, Error as SourceError};

#[derive(Clone, Debug)]
enum LexError {
    Eof,

    IoError {
        cause: io::ErrorKind
    },

    UnexpectedChar(char),
}

impl From<SourceError> for LexError {
    fn from(source: SourceError) -> LexError {        
        match source {
            SourceError::IoError { cause } => LexError::IoError { cause },
        }
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
            LexError::IoError { cause } => write!(f, "I/O error: {}", cause),
            LexError::UnexpectedChar(c) => write!(f, "unexpected character: {}", c),
        }
    }
}

#[derive(Clone, Debug)]
enum Error {
    LexFail { source: LexError },
    MalformedUnicode,
    ParseFail(String),
    UnknownConstant { name: String },
    UnknownFunction { name: String },
}

macro_rules! parse_error {
    ($($arg:tt)*) => {{
        $crate::Error::ParseFail(format!($($arg)*))
    }}
}

macro_rules! try_noeof {
    ($expr:expr) => {
        match $expr {
            Some(Ok(v)) => v,
            Some(Err(v)) => return Err(From::from(v)),
            None => return Err(From::from(LexError::Eof)),
        }
    };
}

impl Error {
    pub fn expect(wanted: &str, got: Token) -> Self {
        Self::ParseFail(format!("expecting {}, got '{}'", wanted, got))
    }
}

impl From<LexError> for Error {
    fn from(source: LexError) -> Self {
        Self::LexFail { source }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Error::LexFail { source } => Some(source),
            _ => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;

        match self {
            LexFail { source } => write!(f, "{}", source),
            MalformedUnicode => write!(f, "malformed unicode detected"),
            ParseFail(s) => write!(f, "parse error: {}", s),
            UnknownConstant { name } => write!(f, "unknown constant: {}", name),
            UnknownFunction { name } => {
                write!(f, "unknown function '{}'", name)
            }
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

struct BaseLex<'a> {
    pub chs: Peekable<Box<dyn Iterator<Item = Result<char, LexError>> + 'a>>,
}

impl <'a> BaseLex<'a> {
    fn new<'b: 'a> (br: impl io::BufRead + 'b) -> Self {
        let base = Chars::new(Box::new(br) as Box<dyn io::BufRead>)
            .map(|el| el.map(|(_, c)| c))
            .map(|el| el.map_err(LexError::from))
            .filter(|el| !matches!(el, Ok('\t' | '\r' | ' ')));

        let boxed: Box<dyn Iterator<Item = _>> = Box::new(base);
        let chs = boxed.peekable();

        BaseLex {
            chs,
        }
    }

    fn next_id_tok(&mut self) -> Result<Token, LexError> {
        let mut id_acc = String::new();

        loop {
            let peek = try_noeof!(self.chs.peek().cloned());

            if !peek.is_alphanumeric() {
                break;
            }

            self.chs.next();

            id_acc.push(peek);
        }

        Ok(Token::Id(id_acc))
    }

    fn next_num_tok(&mut self) -> Result<Token, LexError> {
        let mut val = 0u64;
        let mut dec_div = 1.0f64;
        let mut dec: bool = false;

        loop {
            let next = try_noeof!(self.chs.peek().cloned());
            
            if next == '.' {
                if dec {
                    // Two dots in a numeric token
                    return Err(LexError::UnexpectedChar('.'));
                } else {
                    dec = true; // drop the dot
                    self.chs.next();
                }
            } else if let Some(digit) = next.to_digit(10) {
                // discard the number we've already
                self.chs.next();

                val = 10 * val + digit as u64;

                if dec {
                    dec_div *= 10.0f64;
                }
            } else {
                break;
            }
        }

        Ok(Token::Number(val as f64 / dec_div))
    }
}

impl Iterator for BaseLex<'_> {
    type Item = Result<Token, LexError>;

    fn next(&mut self) -> Option<Result<Token, LexError>> {
        let peek = try_eof!(self.chs.peek().cloned());

        let single_tok = match peek {
            '/' => Token::Div,
            '-' => Token::Minus,
            '+' => Token::Plus,
            '*' => Token::Times,
            '\n' => Token::Newline,
            '(' => Token::OPar,
            ')' => Token::CPar,
            '^' => Token::Caret,
            ch => {
                return if ch.is_digit(10) || ch == '.' {
                    Some(self.next_num_tok())
                } else if ch.is_ascii_alphabetic() {
                    Some(self.next_id_tok())
                } else {
                    Some(Err(LexError::UnexpectedChar(ch)))
                }
            },
        };

        // pop the peeked character
        self.chs.next();

        Some(Ok(single_tok))
    }
}

struct Lex<'a>(Peekable<BaseLex<'a>>);

impl <'a> Lex<'a> {
    pub fn new<'b: 'a>(br: impl io::BufRead + 'b) -> Self {
        br.into()
    }

    pub fn peek(&mut self) -> Option<&Result<Token, LexError>> {
        self.0.peek()
    }
}

impl<'a, 'b: 'a, B: io::BufRead + 'b> From<B> for Lex<'a> {
    fn from(b: B) -> Self {
        Self(BaseLex::new(b).peekable())
    }
}

impl <'a> Iterator for Lex<'a> {
    type Item = <BaseLex<'a> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
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

                args.first()
                    .unwrap()
                    .dump_tree_impl_to(w, padding + 2, true)?;
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
            }
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

fn parse_parens(lex: &mut Lex) -> Result<Node, Error> {
    let par_expr = parse_expr(lex)?;

    match lex.next() {
        Some(Ok(Token::CPar)) => Ok(par_expr),
        Some(Ok(tok)) => Err(Error::expect(")", tok)),
        Some(Err(e)) => Err(e.into()),
        None => Err(parse_error!("unexpected EOF, expecting ')'")),
    }
}

fn parse_func(lex: &mut Lex, id: &str) -> Result<Node, Error> {
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

fn parse_primary(lex: &mut Lex) -> Result<Node, Error> {
    let ntok = match lex.next().transpose()? {
        Some(ntok) => ntok,
        None => return Err(parse_error!("unexpected EOF")),
    };

    match ntok {
        Token::Id(ref id) => {
            if let Some(Ok(Token::OPar)) = lex.peek() {
                return parse_func(lex, id);
            }

            let const_val = match Constant::try_from(id as &str) {
                Ok(c) => c,
                Err(_) => {
                    return Err(parse_error!("unknown identifier '{}'", id,));
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

fn parse_binary(lex: &mut Lex, mut lhs: Node, min_prec: OpPrec) -> Result<Node, Error> {
    let mut cur_op_prec: OpPrec;

    loop {
        let next = match lex.peek() {
            Some(Ok(tok)) => tok,
            Some(Err(err)) => return Err(err.clone().into()),
            None => break,
        };

        cur_op_prec = next.prec();

        if cur_op_prec >= min_prec && next.arity() == OpArity::Binary {
            let op_tok = try_noeof!(lex.next());

            let mut rhs = parse_unary(lex)?;

            if let Some(next) = lex.peek().cloned().transpose()? {
                let next_op_prec = next.prec();
                let next_assoc_right = next.assoc() == OpAssoc::Right;

                if next_op_prec > cur_op_prec || next_assoc_right && next_op_prec == cur_op_prec {
                    rhs = parse_binary(lex, rhs, next_op_prec)?;
                }
            }

            lhs = Node::Binary {
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

fn parse_unary(lex: &mut Lex) -> Result<Node, Error> {
    let peek = lex.peek().cloned().transpose()?;

    match peek {
        Some(next) if next == Token::Minus || next == Token::Plus => {
            let op_top = try_noeof!(lex.next());

            let right_expr = parse_unary(lex)?;

            match op_top {
                Token::Minus => Ok(if let Node::Value(Value::Number(num)) = right_expr {
                    let new_val = Value::Number(-num);

                    Node::Value(new_val)
                } else {
                    Node::Unary {
                        op: UnaryOp::Neg,
                        expr: right_expr.into(),
                    }
                }),
                Token::Plus => Ok(right_expr),
                _ => unreachable!(),
            }
        }
        _ => parse_primary(lex),
    }
}

fn parse_expr(lex: &mut Lex) -> Result<Node, Error> {
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

    let stdin = io::stdin();
    let stdin_guard = stdin.lock();

    let mut lex = Lex::new(stdin_guard);

    loop {
        let discard = match lex.peek() {
            Some(Ok(Token::Newline)) => true,
            None => break,
            _ => false,
        };

        if discard {
            // Discard the newline
            lex.next();
        }

        match parse_expr(&mut lex) {
            Ok(tree) => {
                let res: f64 = tree.eval();

                if print_node {
                    println!("\nTree:\n");
                    tree.dump();
                    println!();
                }

                println!("{}", GPoint(res));

                match lex.next() {
                    Some(Ok(ntok)) => {
                        if ntok != Token::Newline {
                            eprintln!(
                                "error: stray '{}' left in stream after expression",
                                ntok,
                            );

                            status = 1i32;
                            break;
                        } else {
                            status = 0i32; 
                        }
                    }

                    Some(Err(LexError::Eof)) | None => {
                        break;
                    }

                    Some(Err(lerr)) => {
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

    exit(status);
}
