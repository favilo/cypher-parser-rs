use crate::{ast::*, Error};

use bitmask::bitmask;
use boolinator::Boolinator;
use errno::errno;
use libcypher_parser_sys as cypher;
use std::{
    ffi::{CStr, CString},
    ptr::null_mut,
};

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

impl Colorization {
    pub fn to_ptr(&self) -> *const cypher::cypher_parser_colorization {
        unsafe {
            match self {
                Colorization::Uncolorized => cypher::cypher_parser_no_colorization,
                Colorization::Ansi => cypher::cypher_parser_ansi_colorization,
            }
        }
    }
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
        (ptr != null_mut()).as_result(Self { ptr }, Error::ParserError(errno()))
    }

    pub fn set_initial_ordinal(&mut self, n: usize) {
        unsafe {
            cypher::cypher_parser_config_set_initial_ordinal(self.ptr, n as u32);
        }
    }

    pub fn set_initial_position(&mut self, pos: &ParserInputPosition) {
        unsafe {
            cypher::cypher_parser_config_set_initial_position(self.ptr, *pos.0);
        }
    }

    pub fn set_error_colorization(&mut self, colorization: Colorization) {
        unsafe {
            let c = colorization.to_ptr();
            cypher::cypher_parser_config_set_error_colorization(self.ptr, c);
        }
    }
}

#[derive(Debug)]
pub struct ParserInputPosition(Box<cypher::cypher_input_position>);

impl ParserInputPosition {
    pub fn new() -> Self {
        Self(Box::new(cypher::cypher_input_position {
            line: 1,
            column: 1,
            offset: 0,
        }))
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
pub struct ParseError {
    ptr: *const cypher::cypher_parse_error,
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
        input_position: Option<&mut ParserInputPosition>,
        config: Option<&ParserConfig>,
        flags: ParseFlags,
    ) -> Result<Self, Error> {
        let ptr = unsafe {
            cypher::cypher_uparse(
                CString::new(input)?.as_ptr(),
                input.len() as u64,
                input_position
                    .map(|p| &mut *p.0 as *mut cypher::cypher_input_position)
                    .unwrap_or(null_mut()),
                config.map(|c| c.ptr).unwrap_or(null_mut()),
                *flags,
            )
        };
        (ptr != null_mut()).as_result(Self { ptr }, Error::ParserError(errno()))
    }

    pub fn nnodes(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nnodes(self.ptr) as usize }
    }

    pub fn nroots(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nroots(self.ptr) as usize }
    }

    pub fn get_root(&self, idx: usize) -> Result<AstRoot, Error> {
        let ptr = unsafe { cypher::cypher_parse_result_get_root(self.ptr, idx as u32) };
        (ptr != null_mut()).as_result(AstRoot { ptr }, Error::OutOfRangeError(idx))
    }

    pub fn ndirectives(&self) -> usize {
        unsafe { cypher::cypher_parse_result_ndirectives(self.ptr) as usize }
    }

    pub fn get_directive(&self, idx: usize) -> Result<Box<dyn AstNode>, Error> {
        // There is a bug in the underlying C code, if you try to pass one past ndirectives,
        // this seems to try to parse out an ast node of type 113, which doesn't exist...
        // May want to submit a PR.
        let ptr = unsafe { cypher::cypher_parse_result_get_directive(self.ptr, idx as u32) };
        (ptr != null_mut()).as_result(AstRoot { ptr }.to_sub(), Error::OutOfRangeError(idx))
    }

    pub fn directives<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.ndirectives(),
            func: &Self::get_directive,
        }
    }

    pub fn nerrors(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nerrors(self.ptr) as usize }
    }

    pub fn get_error(&self, idx: usize) -> Result<ParseError, Error> {
        let ptr = unsafe { cypher::cypher_parse_result_get_error(self.ptr, idx as u32) };
        (ptr != null_mut()).as_result(ParseError { ptr }, Error::OutOfRangeError(idx))
    }

    pub fn eof(&self) -> bool {
        unsafe { cypher::cypher_parse_result_eof(self.ptr) as bool }
    }

    pub unsafe fn ast_fprint(
        &self,
        width: u32,
        c: Colorization,
        flags: u64,
    ) -> Result<String, Error> {
        let mut mem_ptr: *mut i8 = null_mut();
        let mut size: usize = 0;
        let file = libc::open_memstream(&mut mem_ptr as *mut *mut i8, &mut size as *mut usize);
        cypher::cypher_parse_result_fprint_ast(
            self.ptr,
            file as *mut libcypher_parser_sys::_IO_FILE,
            width,
            c.to_ptr(),
            flags,
        );
        libc::fflush(file);
        let ret = CStr::from_ptr(mem_ptr as *mut i8);
        let ret = ret.to_string_lossy().into_owned();
        libc::fclose(file);
        libc::free(mem_ptr as *mut libc::c_void);
        Ok(ret)
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

        assert!(result.get_directive(0).is_ok());
        assert!(result.get_directive(0)?.is::<AstStatement>());
        assert!(!result.get_directive(0)?.is::<AstCommand>());

        assert!(result.eof());

        let root = result.get_root(0);
        assert!(root.is_ok());

        let root = root?;
        assert_eq!(root.nchildren(), 1);
        let node_type = root.get_type();
        assert_eq!(node_type, AstNodeType::Statement);
        let boxed = root.to_sub();
        let unboxed = boxed.downcast_ref::<AstStatement>();
        assert!(unboxed.is_some());
        assert_eq!(
            unboxed.unwrap().type_str().to_owned(),
            CString::new("statement")?
        );

        let root_sub = root.to_sub();
        let wrong = root_sub.downcast_ref::<AstComment>();
        assert!(wrong.is_none());

        Ok(())
    }

    #[test]
    fn test_fprint() -> Result<(), Error> {
        let mut p = ParserInputPosition::new();
        let result = ParseResult::parse(";", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 1);

        let s = unsafe { result.ast_fprint(10, Colorization::Uncolorized, 0) };
        assert!(s.is_ok());
        assert_eq!(s?, "");

        Ok(())
    }

    #[test]
    fn comment() -> Result<(), Error> {
        let mut p = ParserInputPosition::new();
        let result =
            ParseResult::parse("/*foo*/", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 7);

        let s = unsafe { result.ast_fprint(0, Colorization::Uncolorized, 0) };
        assert!(s.is_ok());

        let expected = "@0  2..5  block_comment  /*foo*/\n";
        assert_eq!(s?, expected);

        Ok(())
    }

    #[test]
    fn error_only() -> Result<(), Error> {
        let mut p = ParserInputPosition::new();
        let result = ParseResult::parse("foo", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 3);

        let s = unsafe { result.ast_fprint(0, Colorization::Uncolorized, 0) };
        assert!(s.is_ok());

        let expected = "@0  0..3  error  >>foo<<\n";
        assert_eq!(s?, expected);
        assert_eq!(result.nerrors(), 1);

        Ok(())
    }

    #[test]
    fn single_statement() -> Result<(), Error> {
        let mut p = ParserInputPosition::new();
        let result =
            ParseResult::parse("return 1", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 8);

        let s = unsafe { result.ast_fprint(0, Colorization::Uncolorized, 0) };
        assert!(s.is_ok());

        let expected = "@0  0..8  statement           body=@1\n\
                        @1  0..8  > query             clauses=[@2]\n\
                        @2  0..8  > > RETURN          projections=[@3]\n\
                        @3  7..8  > > > projection    expression=@4, alias=@5\n\
                        @4  7..8  > > > > integer     1\n\
                        @5  7..8  > > > > identifier  `1`\n";
        assert_eq!(s?, expected);

        Ok(())
    }

    #[test]
    fn single_command() -> Result<(), Error> {
        let mut p = ParserInputPosition::new();
        let result =
            ParseResult::parse(":foo bar", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 8);

        let s = unsafe { result.ast_fprint(0, Colorization::Uncolorized, 0) };
        assert!(s.is_ok());

        let expected = "@0  0..8  command   name=@1, args=[@2]\n\
                        @1  1..4  > string  \"foo\"\n\
                        @2  5..8  > string  \"bar\"\n";
        assert_eq!(s?, expected);

        Ok(())
    }

    #[test]
    fn directives_work() -> Result<(), Error> {
        let mut p = ParserInputPosition::new();
        let result =
            ParseResult::parse("return 1", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 8);
        assert_eq!(result.ndirectives(), 1);
        for directive in result.directives() {
            assert_eq!(directive.get_type(), AstNodeType::Statement);
        }

        Ok(())
    }
}
