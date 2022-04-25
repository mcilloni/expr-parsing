use std::{error, fmt, io};

#[derive(Debug)]
pub enum Error {
    IoError { cause: io::ErrorKind },
}

impl From<io::Error> for Error {
    fn from(cause: io::Error) -> Error {
        Error::IoError { cause: cause.kind() }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::IoError { cause } => cause.fmt(f),
        }
    }
}

pub struct Chars<B: io::BufRead> {
    lines: io::Lines<B>,
    curline: Option<ReadString>,
    lineno: usize,
    lpos: usize,
}

impl<B: io::BufRead> Chars<B> {
    pub fn new(read: B) -> Self {
        Self {
            lines: read.lines(),
            curline: None,
            lineno: 0,
            lpos: 0,
        }
    }

    #[inline]
    fn curline(&mut self) -> Option<&mut ReadString> {
        self.curline.as_mut()
    }

    fn load_next_line(&mut self) -> Option<Result<(), Error>> {
        loop {
            // cut comments away
            let line = cut(try_eof!(self.lines.next()));

            self.lineno += 1;

            if line.chars().any(|ch| !ch.is_whitespace()) {
                self.curline = Some(ReadString::new(line));
                self.lpos = 0;

                break Some(Ok(()));
            }
        }
    }

    #[inline]
    fn pos(&self) -> (usize, usize) {
        (self.lineno, self.lpos)
    }
}

impl<B: io::BufRead> Iterator for Chars<B> {
    type Item = Result<((usize, usize), char), Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curline().is_none() {
            try_eof!(self.load_next_line());
        }

        let mut eol = false;

        let ch = match self.curline() {
            Some(curline) => match curline.next() {
                Some(ch) => ch,
                None => {
                    eol = true;

                    '\n'
                }
            },
            None => panic!(
                "BUG: load_next_line() failed to load a new line, but never returned an error"
            ),
        };

        if eol {
            self.curline = None;
        }

        self.lpos += 1;

        Some(Ok((self.pos(), ch)))
    }
}

pub struct ReadString {
    string: String,
    offset: Option<usize>,
}

impl ReadString {
    fn new(s: String) -> Self {
        Self {
            string: s,
            offset: Some(0),
        }
    }
}

impl Iterator for ReadString {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        match self.offset {
            Some(offset) => {
                let mut ch_in = self.string[offset..].char_indices();

                match ch_in.next() {
                    Some((_, ch)) => {
                        self.offset = ch_in.next().map(|(rpos, _)| offset + rpos);

                        Some(ch)
                    }
                    None => unreachable!(),
                }
            }
            None => None,
        }
    }
}

fn cut(mut s: String) -> String {
    if let Some(pos) = s.find('#') {
        s.truncate(pos)
    }

    s
}
