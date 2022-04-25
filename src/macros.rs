// macro_rules! some {
//     ($expr:expr) => {
//         match $expr {
//             Some(v) => v,
//             None => return Ok(None),
//         }
//     };
// }

macro_rules! try_wrap {
    ($expr:expr) => {
        match $expr {
            Ok(v) => v,
            Err(err) => return Some(Err(From::from(err))),
        }
    };
}

macro_rules! try_opt {
    ($expr:expr) => {
        match $expr {
            Some(res) => Some(try_wrap!(res)),
            None => return None,
        }
    };
}

macro_rules! try_eof {
    ($expr:expr) => {
        match try_opt!($expr) {
            Some(v) => v,
            None => return None,
        }
    };
}
