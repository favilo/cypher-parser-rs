mod create;
mod load_csv;
mod r#match;
mod pattern;
mod query;
mod start;
mod statement;
mod with;

use crate::{
    result::{Colorization, InputRange, Operator},
    CypherParserError,
};

use boolinator::Boolinator;
use libcypher_parser_sys as cypher;
use mopa::mopafy;
use num_derive::FromPrimitive;
use std::{convert::TryFrom, ffi::CStr, fmt, ptr::null_mut};
use strum_macros::Display;

pub use start::*;

#[derive(Debug)]
pub struct AstRoot {
    pub(crate) ptr: *const cypher::cypher_astnode,
}

impl AstNode for AstRoot {
    #[inline]
    fn as_ptr(&self) -> *const cypher::cypher_astnode {
        self.ptr
    }
}

pub struct AstNodeIter<'a, Node, T> {
    pub(crate) obj: &'a T,
    pub(crate) idx: usize,
    pub(crate) max: usize,
    pub(crate) func: &'a dyn Fn(&T, usize) -> Result<Node, CypherParserError>,
}

impl<'a, Node, T> Iterator for AstNodeIter<'a, Node, T> {
    type Item = Node;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.max {
            return None;
        }
        let next = (self.func)(self.obj, self.idx);
        self.idx += 1;
        next.map_or(None, Option::Some)
    }
}

macro_rules! make_ast_nodes {
    ($($enum_name:ident = $id:literal), +,) => {
        paste::paste! {
            pub trait AstNode: mopa::Any {
                fn as_ptr(&self) -> *const cypher::cypher_astnode;

                fn valid_ptr(&self, ptr: *const cypher::cypher_astnode) -> bool {
                   (ptr != null_mut()) && (AstRoot { ptr }.get_type().is_ok())
                }

                fn get_type(&self) -> Result<AstNodeType, CypherParserError> {
                    let t = unsafe { cypher::cypher_astnode_type(self.as_ptr()) };
                    Ok(AstNodeType::try_from(t)?)
                }

                fn instance_of(&self, t: AstNodeType) -> bool {
                    unsafe { cypher::cypher_astnode_instanceof(self.as_ptr(), t as u8) }
                }

                fn type_str<'a>(&'a self) -> &'a CStr {
                    unsafe { CStr::from_ptr(cypher::cypher_astnode_typestr(self.get_type().unwrap() as u8)) }
                }

                unsafe fn ast_fprint(&self, width: u32, c: Colorization, flags: u64) -> Result<String, CypherParserError> {
                    let mut mem_ptr: *mut i8 = null_mut();
                    let mut size: usize = 0;
                    let file = libc::open_memstream(&mut mem_ptr as *mut *mut i8, &mut size as *mut usize);
                    let returned = cypher::cypher_ast_fprint(
                        self.as_ptr(),
                        file as *mut libcypher_parser_sys::_IO_FILE,
                        width,
                        c.to_ptr(),
                        flags
                    );
                    libc::fflush(file);
                    let ret = CStr::from_ptr(mem_ptr as *mut i8);
                    let ret = ret.to_string_lossy().into_owned().clone();
                    libc::fclose(file);
                    libc::free(mem_ptr as *mut libc::c_void);
                    if returned == 0 {
                        Ok(ret)
                    } else {
                        Err(CypherParserError::ParserError(errno::errno()))
                    }
                }

                fn to_sub(&self) -> Result<Box<dyn AstNode>, CypherParserError>
                where
                    Self: Sized,
                {
                    let t = self.get_type()?;
                    let node: Box<dyn AstNode> = match t {
                        $(
                            AstNodeType::[<$enum_name>] => {
                                Box::new([<Ast $enum_name>] {
                                    ptr: self.as_ptr()
                                })
                            }
                        ),*,
                    };
                    Ok(node)
                }

                fn nchildren(&self) -> usize {
                    unsafe { cypher::cypher_astnode_nchildren(self.as_ptr()) as usize }
                }

                fn get_child(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
                    let ptr = unsafe { cypher::cypher_astnode_get_child(self.as_ptr(), idx as u32) };
                    self.valid_ptr(ptr).as_result(
                        AstRoot { ptr }.to_sub()?,
                        CypherParserError::OutOfRangeError(idx)
                    )
                }

                fn range(&self) -> InputRange {
                    let ptr = unsafe { cypher::cypher_astnode_range(self.as_ptr()) };
                    InputRange(ptr)
                }
            }
        }

        mopa::mopafy!(AstNode);

        #[non_exhaustive]
        #[derive(Debug, FromPrimitive, PartialEq, Display)]
        #[repr(u8)]
        pub enum AstNodeType {
            $($enum_name),+
        }

        impl TryFrom<u8> for AstNodeType {
            type Error = CypherParserError;

            fn try_from(i: u8) -> Result<Self, CypherParserError> {
                match i {
                    $($id => Ok(Self::$enum_name)),+,
                    _ => Err(CypherParserError::InvalidType(i as usize)),
                }
            }
        }

        $(
            paste::paste! {
                #[derive(Debug, PartialEq)]
                pub struct [<Ast $enum_name>] {
                    ptr: *const cypher::cypher_astnode,
                }

                impl AstNode for [<Ast $enum_name>] {
                    #[inline]
                    fn as_ptr(&self) -> *const cypher::cypher_astnode {
                        self.ptr
                    }
                }

                #[cfg(test)]
                mod [<$enum_name:snake:lower _tests>] {
                    use super::*;
                    use crate::CypherParserError;
                    #[test]
                    fn [<$enum_name:snake:lower _works>]() -> Result<(), CypherParserError> {
                        unsafe {
                            assert_eq!(
                                AstNodeType::try_from(cypher::[<CYPHER_AST_ $enum_name:snake:upper>])?,
                                AstNodeType::$enum_name
                            );
                        }
                        Ok(())
                    }
                }
            }
        )+

    };
}

make_ast_nodes! {
    Statement = 0,
    StatementOption = 1,
    CypherOption = 2,
    CypherOptionParam = 3,
    ExplainOption = 4,
    ProfileOption = 5,
    SchemaCommand = 6,
    CreateNodePropIndex = 7,
    DropNodePropIndex = 8,
    CreateNodePropConstraint = 9,
    DropNodePropConstraint = 10,
    CreateRelPropConstraint = 11,
    DropRelPropConstraint = 12,
    Query = 13,
    QueryOption = 14,
    UsingPeriodicCommit = 15,
    QueryClause = 16,
    LoadCsv = 17,
    Start = 18,
    StartPoint = 19,
    NodeIndexLookup = 20,
    NodeIndexQuery = 21,
    NodeIdLookup = 22,
    AllNodesScan = 23,
    RelIndexLookup = 24,
    RelIndexQuery = 25,
    RelIdLookup = 26,
    AllRelsScan = 27,
    Match = 28,
    MatchHint = 29,
    UsingIndex = 30,
    UsingJoin = 31,
    UsingScan = 32,
    Merge = 33,
    MergeAction = 34,
    OnMatch = 35,
    OnCreate = 36,
    Create = 37,
    Set = 38,
    SetItem = 39,
    SetProperty = 40,
    SetAllProperties = 41,
    MergeProperties = 42,
    SetLabels = 43,
    Delete = 44,
    Remove = 45,
    RemoveItem = 46,
    RemoveLabels = 47,
    RemoveProperty = 48,
    Foreach = 49,
    With = 50,
    Unwind = 51,
    Call = 52,
    Return = 53,
    Projection = 54,
    OrderBy = 55,
    SortItem = 56,
    Union = 57,
    Expression = 58,
    UnaryOperator = 59,
    BinaryOperator = 60,
    Comparison = 61,
    ApplyOperator = 62,
    ApplyAllOperator = 63,
    PropertyOperator = 64,
    SubscriptOperator = 65,
    SliceOperator = 66,
    LabelsOperator = 67,
    ListComprehension = 68,
    PatternComprehension = 69,
    Case = 70,
    Filter = 71,
    Extract = 72,
    Reduce = 73,
    All = 74,
    Any = 75,
    Single = 76,
    None = 77,
    Collection = 78,
    Map = 79,
    Identifier = 80,
    Parameter = 81,
    String = 82,
    Integer = 83,
    Float = 84,
    Boolean = 85,
    True = 86,
    False = 87,
    Null = 88,
    Label = 89,
    Reltype = 90,
    PropName = 91,
    FunctionName = 92,
    IndexName = 93,
    ProcName = 94,
    Pattern = 95,
    NamedPath = 96,
    ShortestPath = 97,
    PatternPath = 98,
    NodePattern = 99,
    RelPattern = 100,
    Range = 101,
    Command = 102,
    Comment = 103,
    LineComment = 104,
    BlockComment = 105,
    Error = 106,
    MapProjection = 107,
    MapProjectionSelector = 108,
    MapProjectionLiteral = 109,
    MapProjectionProperty = 110,
    MapProjectionIdentifier = 111,
    MapProjectionAllProperties = 112,
}

impl fmt::Debug for dyn AstNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: Make this more useful
        write!(f, "{} node", self.get_type().unwrap())
    }
}

impl AstQuery {
    pub fn noptions(&self) -> usize {
        unsafe { cypher::cypher_ast_query_noptions(self.as_ptr()) as usize }
    }

    pub fn get_option(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_query_get_option(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result(
            AstQueryOption { ptr }.to_sub()?,
            CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn options<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.noptions(),
            func: &Self::get_option,
        }
    }

    pub fn nclauses(&self) -> usize {
        unsafe { cypher::cypher_ast_query_nclauses(self.as_ptr()) as usize }
    }

    pub fn get_clause(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_query_get_clause(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result(
            AstQueryOption { ptr }.to_sub()?,
            CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn clauses<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nclauses(),
            func: &Self::get_clause,
        }
    }
}

impl AstComparison {
    pub fn get_length(&self) -> usize {
        unsafe { cypher::cypher_ast_comparison_get_length(self.as_ptr()) as usize }
    }

    pub fn get_operator(&self, idx: usize) -> Result<Operator, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_comparison_get_operator(self.as_ptr(), idx as u32) };
        Operator::from(ptr)
    }

    pub fn get_argument(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_comparison_get_argument(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstExpression { ptr }.to_sub().unwrap(),
            || CypherParserError::NullPtrError("Comparison::get_argument"),
        )
    }
}

impl AstAny {
    // indicator type
}

impl AstIndexName {
    pub fn get_value(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_index_name_get_value(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

impl AstNone {
    // indicator type
}

impl AstNull {
    // indicator type
}

impl AstReturn {
    pub fn nprojections(&self) -> usize {
        unsafe { cypher::cypher_ast_return_nprojections(self.as_ptr()) as usize }
    }

    pub fn get_projection(&self, idx: usize) -> Result<AstProjection, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_return_get_projection(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result(
            AstProjection { ptr },
            CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn projections<'a>(&'a self) -> AstNodeIter<'a, AstProjection, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nprojections(),
            func: &Self::get_projection,
        }
    }

    pub fn is_distinct(&self) -> bool {
        unsafe { cypher::cypher_ast_return_is_distinct(self.as_ptr()) }
    }

    pub fn has_include_existing(&self) -> bool {
        unsafe { cypher::cypher_ast_return_has_include_existing(self.as_ptr()) }
    }

    pub fn get_order_by(&self) -> Option<AstOrderBy> {
        let ptr = unsafe { cypher::cypher_ast_return_get_order_by(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstOrderBy { ptr })
    }

    pub fn get_skip(&self) -> Option<AstReturn> {
        let ptr = unsafe { cypher::cypher_ast_return_get_skip(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstReturn { ptr })
    }

    pub fn get_limit(&self) -> Option<AstInteger> {
        let ptr = unsafe { cypher::cypher_ast_return_get_limit(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstInteger { ptr })
    }
}

impl AstPropName {
    pub fn get_value(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_prop_name_get_value(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

impl AstProjection {
    pub fn get_alias(&self) -> Option<AstIdentifier> {
        let ptr = unsafe { cypher::cypher_ast_projection_get_alias(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstIdentifier { ptr })
    }

    // TODO: The docs say null isn't possible, but maybe we should not trust that
    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_projection_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstExpression { ptr }.to_sub()?,
            CypherParserError::NullPtrError("Projection::get_expression"),
        )
    }
}

impl AstPropertyOperator {
    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_property_operator_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstExpression { ptr }.to_sub()?,
            CypherParserError::NullPtrError("PropertyOperator::get_expression"),
        )
    }

    pub fn get_prop_name(&self) -> Result<AstPropName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_property_operator_get_prop_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstPropName { ptr },
            CypherParserError::NullPtrError("PropertyOperator::get_prop_name"),
        )
    }
}

impl AstIdentifier {
    pub fn get_name(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_identifier_get_name(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

impl AstString {
    pub fn get_value(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_string_get_value(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

impl AstInteger {
    pub fn get_valuestr(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_integer_get_valuestr(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }

    pub fn get_value(&self) -> Result<isize, CypherParserError> {
        Ok(self.get_valuestr().parse()?)
    }
}

impl AstFloat {
    pub fn get_valuestr(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_float_get_valuestr(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

impl AstLabel {
    pub fn get_name(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_label_get_name(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn statement_body() -> Result<(), CypherParserError> {
        let result = ParseResult::parse("return 1", None, None, ParseOption::Default.into())?;
        assert_eq!(result.ndirectives(), 1);
        let statement = result.get_directive(0)?;
        assert_eq!(statement.get_type()?, AstNodeType::Statement);
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.noptions(), 0);

        let body = statement.get_body()?;
        let body = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(body.get_type()?, AstNodeType::Query);

        assert_eq!(body.nclauses(), 1);
        let mut clauses: Vec<_> = body.clauses().collect();
        let clause = clauses.pop().unwrap();
        assert_eq!(clause.get_type()?, AstNodeType::Return);
        let clause = clause.downcast_ref::<AstReturn>().unwrap();

        assert!(!clause.is_distinct());
        assert!(!clause.has_include_existing());
        assert_eq!(clause.nprojections(), 1);
        let projection = clause.get_projection(0)?;
        assert_eq!(projection.get_type()?, AstNodeType::Projection);

        let alias = projection.get_alias().unwrap();
        assert_eq!(alias.get_type()?, AstNodeType::Identifier);
        assert_eq!(alias.get_name(), "1");

        let expression = projection.get_expression().unwrap();
        assert_eq!(expression.get_type()?, AstNodeType::Integer);
        assert!(expression.instance_of(AstNodeType::Integer));
        assert!(expression.instance_of(AstNodeType::Expression));

        let integer = expression.downcast_ref::<AstInteger>().unwrap();

        assert_eq!(integer.get_valuestr(), "1");

        Ok(())
    }

    #[test]
    fn parse_single_node() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let ast = result.get_directive(0)?;
        let ast = ast.downcast_ref::<AstStatement>().unwrap();
        let query = ast.get_body()?;
        let query = query.downcast_ref::<AstQuery>().unwrap();
        let m = query.get_clause(0)?;
        let m = m.downcast_ref::<AstMatch>().unwrap();

        let pattern = m.get_pattern().unwrap();
        assert_eq!(pattern.get_type()?, AstNodeType::Pattern);

        assert_eq!(pattern.npaths(), 1);
        assert!(pattern.get_path(1).is_err());

        let path = pattern.get_path(0)?;
        assert_eq!(path.get_type()?, AstNodeType::PatternPath);

        Ok(())
    }
}
