use crate::{ast::AstRoot, Error};

use bitmask::bitmask;
use errno::errno;
use libcypher_parser_sys as cypher;
use std::{ffi::CString, ptr::null_mut};

bitmask! {
    pub mask ParseFlags: u64 where flags ParseOption {
        Default = cypher::CYPHER_PARSE_DEFAULT as u64,
        Single = cypher::CYPHER_PARSE_SINGLE as u64,
        OnlyStatements = cypher::CYPHER_PARSE_ONLY_STATEMENTS as u64,
    }
}

pub enum Colorization {
    Uncolorized,
    Ansi,
}

#[derive(Debug)]
pub struct ParserConfig {
    ptr: *mut cypher::cypher_parser_config,
}

impl Drop for ParserConfig {
    fn drop(&mut self) {
        unsafe {
            cypher::cypher_parser_config_free(self.ptr);
        }
    }
}

impl ParserConfig {
    pub fn new() -> Result<Self, Error> {
        let ptr = unsafe { cypher::cypher_parser_new_config() };
        if ptr == null_mut() {
            Err(Error::ParseError(errno()))
        } else {
            Ok(Self { ptr })
        }
    }

    pub fn set_initial_ordinal(&mut self, n: usize) {
        unsafe {
            cypher::cypher_parser_config_set_initial_ordinal(self.ptr, n as u32);
        }
    }

    pub fn set_initial_position(&mut self, pos: &ParserInputPosition) {
        unsafe {
            cypher::cypher_parser_config_set_initial_position(self.ptr, pos.0);
        }
    }

    pub fn set_error_colorization(&mut self, colorization: Colorization) {
        unsafe {
            let c = match colorization {
                Colorization::Uncolorized => cypher::cypher_parser_no_colorization,
                Colorization::Ansi => cypher::cypher_parser_ansi_colorization,
            };
            cypher::cypher_parser_config_set_error_colorization(self.ptr, c);
        }
    }
}

pub struct ParserInputPosition(cypher::cypher_input_position);

impl ParserInputPosition {
    pub fn new() -> Self {
        Self(unsafe { cypher::cypher_input_position_zero })
    }

    pub fn line(&self) -> u32 {
        self.0.line
    }

    pub fn column(&self) -> u32 {
        self.0.column
    }

    pub fn offset(&self) -> u64 {
        self.0.offset
    }
}

#[derive(Debug)]
pub struct ParseResult {
    ptr: *mut cypher::cypher_parse_result,
}

impl Drop for ParseResult {
    fn drop(&mut self) {
        unsafe {
            cypher::cypher_parse_result_free(self.ptr);
        }
    }
}

impl ParseResult {
    pub fn parse(
        input: &str,
        input_position: Option<ParserInputPosition>,
        config: Option<ParserConfig>,
        flags: ParseFlags,
    ) -> Result<Self, Error> {
        let ptr = unsafe {
            cypher::cypher_uparse(
                CString::new(input)?.as_ptr(),
                input.len() as u64,
                input_position
                    .map(|mut p| &mut p.0 as *mut cypher::cypher_input_position)
                    .unwrap_or(null_mut()),
                config.map(|c| c.ptr).unwrap_or(null_mut()),
                *flags,
            )
        };
        if ptr == null_mut() {
            Err(Error::ParseError(errno()))
        } else {
            Ok(Self { ptr })
        }
    }

    pub fn nnodes(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nnodes(self.ptr) as usize }
    }

    pub fn nroots(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nroots(self.ptr) as usize }
    }

    pub fn get_root(&self, idx: usize) -> Result<AstRoot, Error> {
        let ptr = unsafe { cypher::cypher_parse_result_get_root(self.ptr, idx as u32) };
        if ptr == null_mut() {
            Err(Error::OutOfRangeError(idx))
        } else {
            Ok(AstRoot { ptr })
        }
    }

    pub fn ndirectives(&self) -> usize {
        unsafe { cypher::cypher_parse_result_ndirectives(self.ptr) as usize }
    }

    pub fn get_directive(&self, _idx: usize) -> Result<(), Error> {
        todo!()
    }

    pub fn nerrors(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nerrors(self.ptr) as usize }
    }

    pub fn get_error(&self, _idx: usize) -> Result<(), Error> {
        todo!()
    }

    pub fn eof(&self) -> bool {
        unsafe { cypher::cypher_parse_result_eof(self.ptr) as bool }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AstNode, AstNodeType};

    #[test]
    fn it_works() -> Result<(), Error> {
        let result = ParseResult::parse(
            "MATCH (n) RETURN n",
            None,
            None,
            ParseOption::OnlyStatements.into(),
        )?;
        assert_eq!(result.nnodes(), 10);
        assert_eq!(result.nroots(), 1);
        assert_eq!(result.ndirectives(), 1);
        assert_eq!(result.nerrors(), 0);

        assert!(result.eof());

        let root = result.get_root(0);
        assert!(root.is_ok());

        let root = root?;
        let node_type = root.get_type();
        assert_eq!(node_type, AstNodeType::Statement);
        assert_eq!(root.type_str().to_owned(), CString::new("statement")?);

        Ok(())
    }
}
