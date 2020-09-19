use crate::{result::Colorization, Error};

use libcypher_parser_sys as cypher;
use mopa::mopafy;
use num_derive::FromPrimitive;
use std::{convert::TryFrom, ffi::CStr, ptr::null_mut};
use strum_macros::Display;

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
    pub(crate) func: &'a dyn Fn(&T, usize) -> Result<Node, Error>,
}

impl<'a, Node, T> Iterator for AstNodeIter<'a, Node, T> {
    type Item = Node;

    fn next(&mut self) -> Option<Self::Item> {
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

                fn instanceof(&self, t: AstNodeType) -> bool {
                    unsafe { cypher::cypher_astnode_instanceof(self.as_ptr(), t as u8) }
                }

                fn get_type(&self) -> AstNodeType {
                    let t = unsafe { cypher::cypher_astnode_type(self.as_ptr()) };
                    AstNodeType::try_from(t).unwrap()
                }

                fn instance_of(&self, t: AstNodeType) -> bool {
                    unsafe { cypher::cypher_astnode_instanceof(self.as_ptr(), t as u8) }
                }

                fn type_str<'a>(&'a self) -> &'a CStr {
                    unsafe { CStr::from_ptr(cypher::cypher_astnode_typestr(self.get_type() as u8)) }
                }

                unsafe fn ast_fprint(&self, width: u32, c: Colorization, flags: u64) -> Result<String, Error> {
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
                        Err(Error::ParserError(errno::errno()))
                    }
                }

                fn to_sub(&self) -> Box<dyn AstNode>
                where
                    Self: Sized,
                {
                    let t = self.get_type();
                    let node: Box<dyn AstNode> = match t {
                        $(
                            AstNodeType::[<$enum_name>] => {
                                Box::new([<Ast $enum_name>] {
                                    ptr: self.as_ptr()
                                })
                            }
                        ),*,
                    };
                    node
                }

                fn nchildren(&self) -> usize {
                    unsafe { cypher::cypher_astnode_nchildren(self.as_ptr()) as usize }
                }

                fn get_child<'a>(&'a self, idx: usize) -> Result<Box<dyn AstNode>, Error> {
                    let child = unsafe { cypher::cypher_astnode_get_child(self.as_ptr(), idx as u32) };
                    if child == null_mut() {
                        Err(Error::OutOfRangeError(idx))
                    } else {
                        Ok(AstRoot { ptr: child }.to_sub())
                    }
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
            fn try_from(i: u8) -> Result<Self, Error> {
                match i {
                    $($id => Ok(Self::$enum_name)),+,
                    _ => Err(Error::OutOfRangeError(i as usize)),
                }
            }
            type Error = Error;
        }

        $(
            paste::paste! {
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
                    use crate::Error;
                    #[test]
                    fn [<$enum_name:snake:lower _works>]() -> Result<(), Error> {
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

impl AstStatement {
    pub fn noptions(&self) -> usize {
        unsafe { cypher::cypher_ast_statement_noptions(self.as_ptr()) as usize }
    }

    pub fn get_option(&self, idx: usize) -> Result<AstStatementOption, Error> {
        let option = unsafe { cypher::cypher_ast_statement_get_option(self.as_ptr(), idx as u32) };
        if option == null_mut() {
            Err(Error::OutOfRangeError(idx))
        } else {
            Ok(AstStatementOption { ptr: option })
        }
    }

    pub fn options<'a>(&'a self) -> AstNodeIter<'a, AstStatementOption, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            func: &Self::get_option,
        }
    }

    pub fn get_body(&self) -> Box<dyn AstNode> {
        let ptr = unsafe { cypher::cypher_ast_statement_get_body(self.as_ptr()) };
        AstRoot { ptr }.to_sub()
    }
}

impl AstQuery {
    pub fn noptions(&self) -> usize {
        unsafe { cypher::cypher_ast_query_noptions(self.as_ptr()) as usize }
    }

    pub fn get_option(&self, idx: usize) -> Result<AstQueryOption, Error> {
        let option = unsafe { cypher::cypher_ast_query_get_option(self.as_ptr(), idx as u32) };
        if option == null_mut() {
            Err(Error::OutOfRangeError(idx))
        } else {
            Ok(AstQueryOption { ptr: option })
        }
    }

    pub fn options<'a>(&'a self) -> AstNodeIter<'a, AstQueryOption, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            func: &Self::get_option,
        }
    }

    pub fn nclauses(&self) -> usize {
        unsafe { cypher::cypher_ast_query_nclauses(self.as_ptr()) as usize }
    }

    pub fn get_clause(&self, idx: usize) -> Result<Box<dyn AstNode>, Error> {
        let option = unsafe { cypher::cypher_ast_query_get_clause(self.as_ptr(), idx as u32) };
        if option == null_mut() {
            Err(Error::OutOfRangeError(idx))
        } else {
            Ok(AstQueryOption { ptr: option }.to_sub())
        }
    }

    pub fn clauses<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            func: &Self::get_clause,
        }
    }
}

impl AstReturn {
    pub fn nprojections(&self) -> usize {
        unsafe { cypher::cypher_ast_return_nprojections(self.as_ptr()) as usize }
    }

    pub fn get_projection(&self, idx: usize) -> Result<AstProjection, Error> {
        let option = unsafe { cypher::cypher_ast_return_get_projection(self.as_ptr(), idx as u32) };
        if option == null_mut() {
            Err(Error::OutOfRangeError(idx))
        } else {
            Ok(AstProjection { ptr: option })
        }
    }

    pub fn projections<'a>(&'a self) -> AstNodeIter<'a, AstProjection, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            func: &Self::get_projection,
        }
    }
}

impl AstProjection {
    pub fn get_alias(&self) -> Option<AstIdentifier> {
        let ptr = unsafe { cypher::cypher_ast_projection_get_alias(self.as_ptr()) };

        if ptr == null_mut() {
            None
        } else {
            Some(AstIdentifier { ptr })
        }
    }

    // TODO: The docs say null isn't possible, but maybe we should not trust that
    pub fn get_expression(&self) -> Option<Box<dyn AstNode>> {
        let ptr = unsafe { cypher::cypher_ast_projection_get_expression(self.as_ptr()) };

        if ptr == null_mut() {
            None
        } else {
            Some(AstExpression { ptr }.to_sub())
        }
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
    pub fn get_valuestr(&self) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn statement_body() -> Result<(), Error> {
        let result = ParseResult::parse("return 1", None, None, ParseOption::Default.into())?;
        assert_eq!(result.ndirectives(), 1);
        let statement = result.get_directive(0)?;
        assert_eq!(statement.get_type(), AstNodeType::Statement);
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.noptions(), 0);

        let body = statement.get_body();
        let body = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(body.get_type(), AstNodeType::Query);

        assert_eq!(body.nclauses(), 1);
        let clause = body.get_clause(0)?;
        assert_eq!(clause.get_type(), AstNodeType::Return);
        let clause = clause.downcast_ref::<AstReturn>().unwrap();

        assert_eq!(clause.nprojections(), 1);
        let projection = clause.get_projection(0)?;
        assert_eq!(projection.get_type(), AstNodeType::Projection);

        let alias = projection.get_alias().unwrap();
        assert_eq!(alias.get_type(), AstNodeType::Identifier);
        assert_eq!(alias.get_name(), "1");

        let expression = projection.get_expression().unwrap();
        assert_eq!(expression.get_type(), AstNodeType::Integer);
        assert!(expression.instance_of(AstNodeType::Integer));
        assert!(expression.instance_of(AstNodeType::Expression));

        let integer = expression.downcast_ref::<AstInteger>().unwrap();

        assert_eq!(integer.get_valuestr(), "1");

        Ok(())
    }
}
