use errno::Errno;
use libcypher_parser_sys as cypher;
use std::{num::ParseIntError, ffi::{CStr, FromBytesWithNulError, NulError}};
use thiserror::Error;

mod ast;
mod result;

pub use {
    ast::*,
    result::{ParseError, ParseFlags, ParseOption, ParseResult, ParserConfig, InputPosition},
};

#[non_exhaustive]
#[derive(Error, Debug)]
pub enum CypherParserError {
    #[error("parse error: {0}")]
    ParserError(Errno),

    #[error("out of range: {0}")]
    OutOfRangeError(usize),

    #[error("found null ptr where one shouldn't be returned, {0}")]
    NullPtrError(&'static str),

    #[error("wrong ast node type: {0}")]
    WrongAstType(AstNodeType),

    #[error("error creating c-string")]
    CStringError(#[from] NulError),

    #[error("error creating c-string from byte slice")]
    CStringBytesError(#[from] FromBytesWithNulError),

    #[error("error converting string to int")]
    ParseIntError(#[from] ParseIntError),
    // Maybe if try_traits becomes stable
    // #[error("Tried to use None")]
    // NoneError(#[from] NoneError),
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
