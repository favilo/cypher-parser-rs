use errno::Errno;
use libcypher_parser_sys as cypher;
use std::ffi::{CStr, NulError};
use thiserror::Error;

mod ast;
mod result;

pub use result::ParseResult;

#[non_exhaustive]
#[derive(Error, Debug)]
pub enum Error {
    #[error("parse error: {0}")]
    ParseError(Errno),

    #[error("out of range: {0}")]
    OutOfRangeError(usize),

    #[error("error creating c-string")]
    CStringError(#[from] NulError),
}

pub fn libcypher_parser_version() -> String {
    unsafe {
        CStr::from_ptr(cypher::libcypher_parser_version())
            .to_string_lossy()
            .into_owned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!("0.6.0", libcypher_parser_version());
    }
}
