use std::{io, error, fmt, iter::Peekable};

use gpoint::GPoint;

use crate::charsource::{Chars, Error as SourceError};

macro_rules! try_noeof {
    ($expr:expr) => {
        match $expr {
            Some(Ok(v)) => v,
            Some(Err(v)) => return Err(From::from(v)),
            None => return Err(From::from($crate::lex::Error::Eof)),
        }
    };
}

#[derive(Clone, Debug)]
pub enum Error {
    Eof,

    IoError {
        cause: io::ErrorKind
    },

    UnexpectedChar(char),
}

impl From<SourceError> for Error {
    fn from(source: SourceError) -> Error {        
        match source {
            SourceError::IoError { cause } => Error::IoError { cause },
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Eof => write!(f, "reached end of file"),
            Error::IoError { cause } => write!(f, "I/O error: {}", cause),
            Error::UnexpectedChar(c) => write!(f, "unexpected character: {}", c),
        }
    }
}

pub struct BaseLex<'a> {
    pub chs: Peekable<Box<dyn Iterator<Item = Result<char, Error>> + 'a>>,
}

impl <'a> BaseLex<'a> {
    fn new<'b: 'a> (br: impl io::BufRead + 'b) -> Self {
        let base = Chars::new(Box::new(br) as Box<dyn io::BufRead>)
            .map(|el| el.map(|(_, c)| c))
            .map(|el| el.map_err(Error::from))
            .filter(|el| !matches!(el, Ok('\t' | '\r' | ' ')));

        let boxed: Box<dyn Iterator<Item = _>> = Box::new(base);
        let chs = boxed.peekable();

        BaseLex {
            chs,
        }
    }

    fn next_id_tok(&mut self) -> Result<Token, Error> {
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

    fn next_num_tok(&mut self) -> Result<Token, Error> {
        let mut val = 0u64;
        let mut dec_div = 1.0f64;
        let mut dec: bool = false;

        loop {
            let next = try_noeof!(self.chs.peek().cloned());
            
            if next == '.' {
                if dec {
                    // Two dots in a numeric token
                    return Err(Error::UnexpectedChar('.'));
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
    type Item = Result<Token, Error>;

    fn next(&mut self) -> Option<Result<Token, Error>> {
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
                    Some(Err(Error::UnexpectedChar(ch)))
                }
            },
        };

        // pop the peeked character
        self.chs.next();

        Some(Ok(single_tok))
    }
}

pub struct Lex<'a>(Peekable<BaseLex<'a>>);

impl <'a> Lex<'a> {
    pub fn new<'b: 'a>(br: impl io::BufRead + 'b) -> Self {
        br.into()
    }

    pub fn peek(&mut self) -> Option<&Result<Token, Error>> {
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
pub enum Token {
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