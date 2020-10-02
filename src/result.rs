use crate::{ast::*, CypherParserError};

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
    pub fn new() -> Result<Self, CypherParserError> {
        let ptr = unsafe { cypher::cypher_parser_new_config() };
        (ptr != null_mut()).as_result(Self { ptr }, CypherParserError::ParserError(errno()))
    }

    pub fn set_initial_ordinal(&mut self, n: usize) {
        unsafe {
            cypher::cypher_parser_config_set_initial_ordinal(self.ptr, n as u32);
        }
    }

    pub fn set_initial_position(&mut self, pos: &InputPosition) {
        unsafe {
            cypher::cypher_parser_config_set_initial_position(self.ptr, pos.0);
        }
    }

    pub fn set_error_colorization(&mut self, colorization: Colorization) {
        unsafe {
            let c = colorization.to_ptr();
            cypher::cypher_parser_config_set_error_colorization(self.ptr, c);
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum RelDirection {
    OutBound,
    InBound,
    Bidirectional,
}

impl Into<RelDirection> for cypher::cypher_rel_direction {
    fn into(self) -> RelDirection {
        match self {
            cypher::cypher_rel_direction::CYPHER_REL_OUTBOUND => RelDirection::OutBound,
            cypher::cypher_rel_direction::CYPHER_REL_INBOUND => RelDirection::InBound,
            cypher::cypher_rel_direction::CYPHER_REL_BIDIRECTIONAL => RelDirection::Bidirectional,
        }
    }
}

impl Into<cypher::cypher_rel_direction> for RelDirection {
    fn into(self) -> cypher::cypher_rel_direction {
        match self {
            RelDirection::OutBound => cypher::cypher_rel_direction::CYPHER_REL_OUTBOUND,
            RelDirection::InBound => cypher::cypher_rel_direction::CYPHER_REL_INBOUND,
            RelDirection::Bidirectional => cypher::cypher_rel_direction::CYPHER_REL_BIDIRECTIONAL,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Operator {
    Or,
    Xor,
    And,
    Not,
    Equal,
    NEqual,
    Lt,
    Gt,
    LtE,
    GtE,
    Plus,
    Minus,
    Mult,
    Div,
    Mod,
    Pow,
    UPlus,
    UMinus,
    Regex,
    In,
    StartsWith,
    EndsWith,
    Contains,
    IsNull,
    IsNotNull,
    MapProjection,
    Subscript,
    Property,
    Label,
}

impl Operator {
    pub fn from(other: *const cypher::cypher_operator) -> Result<Self, CypherParserError> {
        unsafe {
            if other == cypher::CYPHER_OP_OR {
                return Ok(Self::Or);
            }
            if other == cypher::CYPHER_OP_XOR {
                return Ok(Self::Xor);
            }
            if other == cypher::CYPHER_OP_AND {
                return Ok(Self::And);
            }
            if other == cypher::CYPHER_OP_NOT {
                return Ok(Self::Not);
            }
            if other == cypher::CYPHER_OP_EQUAL {
                return Ok(Self::Equal);
            }
            if other == cypher::CYPHER_OP_NEQUAL {
                return Ok(Self::NEqual);
            }
            if other == cypher::CYPHER_OP_LT {
                return Ok(Self::Lt);
            }
            if other == cypher::CYPHER_OP_GT {
                return Ok(Self::Gt);
            }
            if other == cypher::CYPHER_OP_LTE {
                return Ok(Self::LtE);
            }
            if other == cypher::CYPHER_OP_GTE {
                return Ok(Self::GtE);
            }
            if other == cypher::CYPHER_OP_PLUS {
                return Ok(Self::Plus);
            }
            if other == cypher::CYPHER_OP_MINUS {
                return Ok(Self::Minus);
            }
            if other == cypher::CYPHER_OP_MULT {
                return Ok(Self::Mult);
            }
            if other == cypher::CYPHER_OP_DIV {
                return Ok(Self::Div);
            }
            if other == cypher::CYPHER_OP_MOD {
                return Ok(Self::Mod);
            }
            if other == cypher::CYPHER_OP_POW {
                return Ok(Self::Pow);
            }
            if other == cypher::CYPHER_OP_UNARY_PLUS {
                return Ok(Self::UPlus);
            }
            if other == cypher::CYPHER_OP_UNARY_MINUS {
                return Ok(Self::UMinus);
            }
            if other == cypher::CYPHER_OP_REGEX {
                return Ok(Self::Regex);
            }
            if other == cypher::CYPHER_OP_IN {
                return Ok(Self::In);
            }
            if other == cypher::CYPHER_OP_STARTS_WITH {
                return Ok(Self::StartsWith);
            }
            if other == cypher::CYPHER_OP_ENDS_WITH {
                return Ok(Self::EndsWith);
            }
            if other == cypher::CYPHER_OP_CONTAINS {
                return Ok(Self::Contains);
            }
            if other == cypher::CYPHER_OP_IS_NULL {
                return Ok(Self::IsNull);
            }
            if other == cypher::CYPHER_OP_IS_NOT_NULL {
                return Ok(Self::IsNotNull);
            }
            if other == cypher::CYPHER_OP_MAP_PROJECTION {
                return Ok(Self::MapProjection);
            }
            if other == cypher::CYPHER_OP_SUBSCRIPT {
                return Ok(Self::Subscript);
            }
            if other == cypher::CYPHER_OP_PROPERTY {
                return Ok(Self::Property);
            }
            if other == cypher::CYPHER_OP_LABEL {
                return Ok(Self::Label);
            }
            return Err(CypherParserError::NullPtrError("Operator::from"));
        }
    }

    pub(crate) fn to_c(&self) -> *const cypher::cypher_operator {
        unsafe {
            match self {
                Operator::Or => cypher::CYPHER_OP_OR,
                Operator::Xor => cypher::CYPHER_OP_XOR,
                Operator::And => cypher::CYPHER_OP_AND,
                Operator::Not => cypher::CYPHER_OP_NOT,
                Operator::Equal => cypher::CYPHER_OP_EQUAL,
                Operator::NEqual => cypher::CYPHER_OP_NEQUAL,
                Operator::Lt => cypher::CYPHER_OP_LT,
                Operator::Gt => cypher::CYPHER_OP_GT,
                Operator::LtE => cypher::CYPHER_OP_LTE,
                Operator::GtE => cypher::CYPHER_OP_GTE,
                Operator::Plus => cypher::CYPHER_OP_PLUS,
                Operator::Minus => cypher::CYPHER_OP_MINUS,
                Operator::Mult => cypher::CYPHER_OP_MULT,
                Operator::Div => cypher::CYPHER_OP_DIV,
                Operator::Mod => cypher::CYPHER_OP_MOD,
                Operator::Pow => cypher::CYPHER_OP_POW,
                Operator::UPlus => cypher::CYPHER_OP_UNARY_PLUS,
                Operator::UMinus => cypher::CYPHER_OP_UNARY_MINUS,
                Operator::Regex => cypher::CYPHER_OP_REGEX,
                Operator::In => cypher::CYPHER_OP_IN,
                Operator::StartsWith => cypher::CYPHER_OP_STARTS_WITH,
                Operator::EndsWith => cypher::CYPHER_OP_ENDS_WITH,
                Operator::Contains => cypher::CYPHER_OP_CONTAINS,
                Operator::IsNull => cypher::CYPHER_OP_IS_NULL,
                Operator::IsNotNull => cypher::CYPHER_OP_IS_NOT_NULL,
                Operator::MapProjection => cypher::CYPHER_OP_MAP_PROJECTION,
                Operator::Subscript => cypher::CYPHER_OP_SUBSCRIPT,
                Operator::Property => cypher::CYPHER_OP_PROPERTY,
                Operator::Label => cypher::CYPHER_OP_LABEL,
            }
        }
    }
}

#[derive(Debug)]
pub struct InputPosition(cypher::cypher_input_position);

impl InputPosition {
    pub fn new() -> Self {
        Self(cypher::cypher_input_position {
            line: 1,
            column: 1,
            offset: 0,
        })
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

pub struct InputRange(pub(crate) cypher::cypher_input_range);

impl InputRange {
    pub fn start(&self) -> InputPosition {
        InputPosition(self.0.start)
    }

    pub fn end(&self) -> InputPosition {
        InputPosition(self.0.end)
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
        input_position: Option<&mut InputPosition>,
        config: Option<&ParserConfig>,
        flags: ParseFlags,
    ) -> Result<Self, CypherParserError> {
        let ptr = unsafe {
            cypher::cypher_uparse(
                CString::new(input)?.as_ptr(),
                input.len() as u64,
                input_position
                    .map(|p| &mut p.0 as *mut cypher::cypher_input_position)
                    .unwrap_or(null_mut()),
                config.map(|c| c.ptr).unwrap_or(null_mut()),
                *flags,
            )
        };
        (ptr != null_mut()).as_result(Self { ptr }, CypherParserError::ParserError(errno()))
    }

    pub fn nnodes(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nnodes(self.ptr) as usize }
    }

    pub fn nroots(&self) -> usize {
        unsafe { cypher::cypher_parse_result_nroots(self.ptr) as usize }
    }

    pub fn get_root(&self, idx: usize) -> Result<AstRoot, CypherParserError> {
        let ptr = unsafe { cypher::cypher_parse_result_get_root(self.ptr, idx as u32) };
        (ptr != null_mut()).as_result(AstRoot { ptr }, CypherParserError::OutOfRangeError(idx))
    }

    pub fn ndirectives(&self) -> usize {
        unsafe { cypher::cypher_parse_result_ndirectives(self.ptr) as usize }
    }

    pub fn get_directive(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        // There is a bug in the underlying C code, if you try to pass one past ndirectives,
        // this seems to try to parse out an ast node of type 113, which doesn't exist...
        // May want to submit a PR.
        let ptr = unsafe { cypher::cypher_parse_result_get_directive(self.ptr, idx as u32) };
        (ptr != null_mut()).as_result(
            AstRoot { ptr }.to_sub()?,
            CypherParserError::OutOfRangeError(idx),
        )
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

    pub fn get_error(&self, idx: usize) -> Result<ParseError, CypherParserError> {
        let ptr = unsafe { cypher::cypher_parse_result_get_error(self.ptr, idx as u32) };
        (ptr != null_mut()).as_result(ParseError { ptr }, CypherParserError::OutOfRangeError(idx))
    }

    pub fn eof(&self) -> bool {
        unsafe { cypher::cypher_parse_result_eof(self.ptr) as bool }
    }

    pub unsafe fn ast_fprint(
        &self,
        width: u32,
        c: Colorization,
        flags: u64,
    ) -> Result<String, CypherParserError> {
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
    fn it_works() -> Result<(), CypherParserError> {
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
        assert!(root.get_child(0).is_ok());
        let node_type = root.get_type()?;
        assert_eq!(node_type, AstNodeType::Statement);
        let boxed = root.to_sub()?;
        let unboxed = boxed.downcast_ref::<AstStatement>();
        assert!(unboxed.is_some());
        assert_eq!(
            unboxed.unwrap().type_str().to_owned(),
            CString::new("statement")?
        );

        let root_sub = root.to_sub()?;
        let wrong = root_sub.downcast_ref::<AstComment>();
        assert!(wrong.is_none());

        Ok(())
    }

    #[test]
    fn test_fprint() -> Result<(), CypherParserError> {
        let mut p = InputPosition::new();
        let result = ParseResult::parse(";", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 1);

        let s = unsafe { result.ast_fprint(10, Colorization::Uncolorized, 0) };
        assert!(s.is_ok());
        assert_eq!(s?, "");

        Ok(())
    }

    #[test]
    fn comment() -> Result<(), CypherParserError> {
        let mut p = InputPosition::new();
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
    fn error_only() -> Result<(), CypherParserError> {
        let mut p = InputPosition::new();
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
    fn single_statement() -> Result<(), CypherParserError> {
        let mut p = InputPosition::new();
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
    fn single_command() -> Result<(), CypherParserError> {
        let mut p = InputPosition::new();
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
        let directive = result.get_directive(0)?;
        let s = unsafe { directive.ast_fprint(0, Colorization::Uncolorized, 0) };
        assert_eq!(s?, expected);

        Ok(())
    }

    #[test]
    fn directives_work() -> Result<(), CypherParserError> {
        let mut p = InputPosition::new();
        let result =
            ParseResult::parse("return 1", Some(&mut p), None, ParseOption::Default.into())?;
        assert_eq!(p.0.line, 1);
        assert_eq!(p.0.offset, 8);
        assert_eq!(result.ndirectives(), 1);
        for directive in result.directives() {
            assert_eq!(directive.get_type()?, AstNodeType::Statement);
        }

        Ok(())
    }
}
