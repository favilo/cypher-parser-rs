use super::*;
use crate::result::RelDirection;
use std::ops::Deref;

impl AstPattern {
    pub fn npaths(&self) -> usize {
        unsafe { cypher::cypher_ast_pattern_npaths(self.as_ptr()) as usize }
    }

    pub fn get_path(&self, idx: usize) -> Result<AstPatternPath, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_pattern_get_path(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result(
            AstPatternPath { ptr },
            CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn paths<'a>(&'a self) -> AstNodeIter<'a, AstPatternPath, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.npaths(),
            func: &Self::get_path,
        }
    }
}

impl AstPatternPath {
    pub fn nelements(&self) -> usize {
        unsafe { cypher::cypher_ast_pattern_path_nelements(self.as_ptr()) as usize }
    }
    pub fn get_element(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_pattern_path_get_element(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstPatternPath { ptr }.to_sub().unwrap(),
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn elements<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nelements(),
            func: &Self::get_element,
        }
    }

    pub fn is_named(&self) -> bool {
        self.get_type().unwrap() == AstNodeType::NamedPath
    }

    pub fn to_named(&self) -> Result<AstNamedPath, CypherParserError> {
        self.is_named().as_result_from(
            || AstNamedPath { ptr: self.as_ptr() },
            || CypherParserError::InvalidType(self.get_type().unwrap() as usize),
        )
    }

    pub fn is_shortest(&self) -> bool {
        self.get_type().unwrap() == AstNodeType::ShortestPath
    }

    pub fn to_shortest(&self) -> Result<AstShortestPath, CypherParserError> {
        self.is_named().as_result_from(
            || AstShortestPath { ptr: self.as_ptr() },
            || CypherParserError::InvalidType(self.get_type().unwrap() as usize),
        )
    }
}

impl AstNamedPath {
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_named_path_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstIdentifier { ptr },
            || CypherParserError::NullPtrError("NamedPath::get_identifier"),
        )
    }

    pub fn get_path(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_named_path_get_path(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstPatternPath { ptr }.to_sub().unwrap(),
            || CypherParserError::NullPtrError("NamedPath::get_path"),
        )
    }

    pub fn nelements(&self) -> usize {
        unsafe { cypher::cypher_ast_pattern_path_nelements(self.as_ptr()) as usize }
    }

    pub fn get_element(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_pattern_path_get_element(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstPatternPath { ptr }.to_sub().unwrap(),
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn elements<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nelements(),
            func: &Self::get_element,
        }
    }
}

impl AstShortestPath {
    pub fn is_single(&self) -> bool {
        unsafe { cypher::cypher_ast_shortest_path_is_single(self.as_ptr()) }
    }

    pub fn get_path(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_shortest_path_get_path(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstPatternPath { ptr }.to_sub().unwrap(),
            || CypherParserError::NullPtrError("NamedPath::get_path"),
        )
    }

    pub fn nelements(&self) -> usize {
        unsafe { cypher::cypher_ast_pattern_path_nelements(self.as_ptr()) as usize }
    }

    pub fn get_element(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_pattern_path_get_element(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstPatternPath { ptr }.to_sub().unwrap(),
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn elements<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nelements(),
            func: &Self::get_element,
        }
    }
}

impl AstNodePattern {
    pub fn get_identifier(&self) -> Option<AstIdentifier> {
        let ptr = unsafe { cypher::cypher_ast_node_pattern_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstIdentifier { ptr })
    }

    pub fn get_label(&self, idx: usize) -> Result<AstLabel, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_pattern_get_label(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstLabel { ptr },
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn nlabels(&self) -> usize {
        unsafe { cypher::cypher_ast_node_pattern_nlabels(self.as_ptr()) as usize }
    }

    pub fn labels<'a>(&'a self) -> AstNodeIter<'a, AstLabel, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nlabels(),
            func: &Self::get_label,
        }
    }

    pub fn get_properties(&self) -> Option<Box<dyn AstNode>> {
        let ptr = unsafe { cypher::cypher_ast_node_pattern_get_properties(self.as_ptr()) };
        self.valid_ptr(ptr)
            .as_some_from(|| AstRoot { ptr }.to_sub().unwrap())
    }
}

impl AstRelPattern {
    pub fn get_direction(&self) -> RelDirection {
        unsafe { cypher::cypher_ast_rel_pattern_get_direction(self.as_ptr()).into() }
    }

    pub fn get_identifier(&self) -> Option<AstIdentifier> {
        let ptr = unsafe { cypher::cypher_ast_rel_pattern_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstIdentifier { ptr })
    }

    pub fn nreltypes(&self) -> usize {
        unsafe { cypher::cypher_ast_rel_pattern_nreltypes(self.as_ptr()) as usize }
    }

    pub fn get_reltype(&self, idx: usize) -> Result<AstReltype, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_pattern_get_reltype(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstReltype { ptr },
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn reltypes<'a>(&'a self) -> AstNodeIter<'a, AstReltype, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nreltypes(),
            func: &Self::get_reltype,
        }
    }

    pub fn get_varlength(&self) -> Option<AstRange> {
        let ptr = unsafe { cypher::cypher_ast_rel_pattern_get_varlength(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstRange { ptr })
    }

    pub fn get_properties(&self) -> Option<Box<dyn AstNode>> {
        let ptr = unsafe { cypher::cypher_ast_rel_pattern_get_properties(self.as_ptr()) };
        self.valid_ptr(ptr)
            .as_some_from(|| AstRoot { ptr }.to_sub().unwrap())
    }
}

impl AstReltype {
    pub fn get_name(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_reltype_get_name(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

impl AstMap {
    pub fn get_key(&self, idx: usize) -> Result<AstPropName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_map_get_key(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstPropName { ptr },
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn get_value(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_map_get_value(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstExpression { ptr }.to_sub().unwrap(),
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn nentries(&self) -> usize {
        unsafe { cypher::cypher_ast_map_nentries(self.as_ptr()) as usize }
    }

    pub fn entries<'a>(&'a self) -> AstNodeIter<'a, (AstPropName, Box<dyn AstNode>), Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nentries(),
            func: &|o, i| Ok((o.get_key(i)?, o.get_value(i)?)),
        }
    }
}

impl AstParameter {
    pub fn get_name(&self) -> String {
        let s = unsafe {
            let s = cypher::cypher_ast_parameter_get_name(self.as_ptr());
            CStr::from_ptr(s)
        };
        s.to_string_lossy().into_owned()
    }
}

impl AstRange {
    pub fn get_start(&self) -> Option<AstInteger> {
        let ptr = unsafe { cypher::cypher_ast_range_get_start(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstInteger { ptr })
    }

    pub fn get_end(&self) -> Option<AstInteger> {
        let ptr = unsafe { cypher::cypher_ast_range_get_end(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstInteger { ptr })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_single_node() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        assert_eq!(paths[0].nelements(), 1);
        assert_eq!(
            paths[0].get_element(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );

        let nodes: Vec<_> = paths[0].elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        assert_eq!(
            node.get_label(0).unwrap_err(),
            CypherParserError::OutOfRangeError(0)
        );
        assert!(node.get_properties().is_none());

        Ok(())
    }

    #[test]
    fn parse_labeled_node() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n:Foo) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        assert_eq!(paths[0].nelements(), 1);
        assert_eq!(
            paths[0].get_element(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );

        let nodes: Vec<_> = paths[0].elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 1);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels[0].get_name(), "Foo");
        assert!(node.get_properties().is_none());

        Ok(())
    }

    #[test]
    fn parse_multiple_labeled_node() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n:Foo:Bar) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        assert_eq!(paths[0].nelements(), 1);
        assert_eq!(
            paths[0].get_element(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );

        let nodes: Vec<_> = paths[0].elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 2);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels[0].get_name(), "Foo");
        assert_eq!(labels[1].get_name(), "Bar");
        assert!(node.get_properties().is_none());

        Ok(())
    }

    #[test]
    fn parse_node_with_map_props() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n:Person {name: 'Hunter'}) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        assert_eq!(paths[0].nelements(), 1);
        assert_eq!(
            paths[0].get_element(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );

        let nodes: Vec<_> = paths[0].elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 1);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels[0].get_name(), "Person");

        let props = node.get_properties().unwrap();
        assert_eq!(props.get_type()?, AstNodeType::Map);

        let map = props.downcast_ref::<AstMap>().unwrap();
        assert_eq!(map.nentries(), 1);
        assert_eq!(
            map.get_key(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        assert_eq!(
            map.get_value(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );

        let entries: Vec<_> = map.entries().collect();
        let (key, value) = &entries[0];
        assert_eq!(key.get_value(), "name");
        assert_eq!(value.get_type()?, AstNodeType::String);
        let value = value.downcast_ref::<AstString>().unwrap();
        assert_eq!(value.get_value(), "Hunter");

        Ok(())
    }

    #[test]
    fn parse_node_with_param_props() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n:Person {param}) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        assert_eq!(paths[0].nelements(), 1);
        assert_eq!(
            paths[0].get_element(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );

        let nodes: Vec<_> = paths[0].elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 1);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels[0].get_name(), "Person");

        let props = node.get_properties().unwrap();
        assert_eq!(props.get_type()?, AstNodeType::Parameter);
        let props = props.downcast_ref::<AstParameter>().unwrap();
        assert_eq!(props.get_name(), "param");

        Ok(())
    }

    #[test]
    fn parse_single_rel() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n)-[:Foo]->(m) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.nelements(), 3);
        assert_eq!(
            path.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let node = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(node.get_direction(), RelDirection::OutBound);
        assert!(node.get_identifier().is_none());

        assert_eq!(node.nreltypes(), 1);
        assert_eq!(
            node.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = node.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        assert!(node.get_varlength().is_none());

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }

    #[test]
    fn parse_varlength_rel() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n)-[r:Foo*]-(m) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.nelements(), 3);
        assert_eq!(
            path.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let node = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(node.get_direction(), RelDirection::Bidirectional);
        let id = node.get_identifier().unwrap();
        assert_eq!(id.get_name(), "r");

        assert_eq!(node.nreltypes(), 1);
        assert_eq!(
            node.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = node.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        let varlength = node.get_varlength().unwrap();
        assert_eq!(varlength.get_type()?, AstNodeType::Range);
        assert!(varlength.get_start().is_none());
        assert!(varlength.get_end().is_none());

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }

    #[test]
    fn parse_varlength_rel_with_bounded_start() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n)-[r:Foo*5..]-(m) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.nelements(), 3);
        assert_eq!(
            path.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let node = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(node.get_direction(), RelDirection::Bidirectional);
        let id = node.get_identifier().unwrap();
        assert_eq!(id.get_name(), "r");

        assert_eq!(node.nreltypes(), 1);
        assert_eq!(
            node.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = node.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        let varlength = node.get_varlength().unwrap();
        assert_eq!(varlength.get_type()?, AstNodeType::Range);
        let start = varlength.get_start().unwrap();
        assert_eq!(start.get_type()?, AstNodeType::Integer);
        assert_eq!(start.get_value()?, 5);
        assert!(varlength.get_end().is_none());

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }

    #[test]
    fn parse_varlength_rel_with_bounded_end() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n)-[r:Foo*..9]-(m) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.nelements(), 3);
        assert_eq!(
            path.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let node = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(node.get_direction(), RelDirection::Bidirectional);
        let id = node.get_identifier().unwrap();
        assert_eq!(id.get_name(), "r");

        assert_eq!(node.nreltypes(), 1);
        assert_eq!(
            node.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = node.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        let varlength = node.get_varlength().unwrap();
        assert_eq!(varlength.get_type()?, AstNodeType::Range);
        assert!(varlength.get_start().is_none());
        let end = varlength.get_end().unwrap();
        assert_eq!(end.get_type()?, AstNodeType::Integer);
        assert_eq!(end.get_value()?, 9);

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }

    #[test]
    fn parse_varlength_rel_with_fixed_range() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n)-[r:Foo*7]-(m) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.nelements(), 3);
        assert_eq!(
            path.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let node = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(node.get_direction(), RelDirection::Bidirectional);
        let id = node.get_identifier().unwrap();
        assert_eq!(id.get_name(), "r");

        assert_eq!(node.nreltypes(), 1);
        assert_eq!(
            node.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = node.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        let varlength = node.get_varlength().unwrap();
        assert_eq!(varlength.get_type()?, AstNodeType::Range);

        let start = varlength.get_start().unwrap();
        let end = varlength.get_end().unwrap();
        assert_eq!(end.get_type()?, AstNodeType::Integer);
        assert_eq!(end.get_value()?, 7);
        assert_eq!(end, start);
        assert_eq!(end.as_ptr(), start.as_ptr());

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }

    #[test]
    fn parse_rel_with_map_props() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "RETURN (n)-[:Foo {start:1999, end:2000}]->(m) AS p;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Return);

        let m: &AstReturn = clause.downcast_ref().unwrap();

        let projection = m.get_projection(0).unwrap();
        let pattern_path = projection.get_expression().unwrap();
        assert_eq!(pattern_path.get_type()?, AstNodeType::PatternPath);

        let path = pattern_path.downcast_ref::<AstPatternPath>().unwrap();
        assert_eq!(path.nelements(), 3);
        assert_eq!(
            path.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let rel = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(rel.get_direction(), RelDirection::OutBound);
        let id = rel.get_identifier();
        assert!(id.is_none());

        assert_eq!(rel.nreltypes(), 1);
        assert_eq!(
            rel.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = rel.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        assert!(rel.get_varlength().is_none());

        let props = rel.get_properties().unwrap();
        assert_eq!(props.get_type()?, AstNodeType::Map);
        let map = props.downcast_ref::<AstMap>().unwrap();
        assert_eq!(map.nentries(), 2);

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);
        assert_eq!(
            map.get_key(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );
        assert_eq!(
            map.get_value(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );

        let entries: Vec<_> = map.entries().collect();
        let (key, value) = &entries[0];
        assert_eq!(key.get_value(), "start");
        assert_eq!(value.get_type()?, AstNodeType::Integer);
        let value = value.downcast_ref::<AstInteger>().unwrap();
        assert_eq!(value.get_value()?, 1999);

        let (key, value) = &entries[1];
        assert_eq!(key.get_value(), "end");
        assert_eq!(value.get_type()?, AstNodeType::Integer);
        let value = value.downcast_ref::<AstInteger>().unwrap();
        assert_eq!(value.get_value()?, 2000);

        Ok(())
    }

    #[test]
    fn parse_named_path() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH p = (n)-[:Foo]->(m) RETURN p;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.get_type()?, AstNodeType::NamedPath);
        let path = path.to_named()?;
        assert_eq!(path.get_identifier()?.get_name(), "p");

        assert_eq!(path.nelements(), 3);
        assert_eq!(
            path.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let rel = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(rel.get_direction(), RelDirection::OutBound);
        let id = rel.get_identifier();
        assert!(id.is_none());

        assert_eq!(rel.nreltypes(), 1);
        assert_eq!(
            rel.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = rel.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        assert!(rel.get_varlength().is_none());

        assert!(rel.get_properties().is_none());

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }

    #[test]
    fn parse_shortest_path() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH p = shortestPath((n)-[:Foo]->(m)) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.get_type()?, AstNodeType::NamedPath);
        let npath = path.to_named()?;
        assert_eq!(npath.get_identifier()?.get_name(), "p");

        assert_eq!(npath.nelements(), 3);
        assert_eq!(
            npath.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let path = npath.get_path()?;
        assert_eq!(path.get_type()?, AstNodeType::ShortestPath);
        let path = path.downcast_ref::<AstShortestPath>().unwrap();

        assert!(path.is_single());

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let rel = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(rel.get_direction(), RelDirection::OutBound);
        let id = rel.get_identifier();
        assert!(id.is_none());

        assert_eq!(rel.nreltypes(), 1);
        assert_eq!(
            rel.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = rel.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        assert!(rel.get_varlength().is_none());

        assert!(rel.get_properties().is_none());

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }

    #[test]
    fn parse_all_shortest_path() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH p = allShortestPaths((n)-[:Foo]->(m)) RETURN n;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::Match);

        let m: &AstMatch = clause.downcast_ref().unwrap();

        let pattern = m.get_pattern().unwrap();

        assert_eq!(pattern.npaths(), 1);
        assert_eq!(
            pattern.get_path(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let paths: Vec<_> = pattern.paths().collect();
        let path = &paths[0];
        assert_eq!(path.get_type()?, AstNodeType::NamedPath);
        let npath = path.to_named()?;
        assert_eq!(npath.get_identifier()?.get_name(), "p");

        assert_eq!(npath.nelements(), 3);
        assert_eq!(
            npath.get_element(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let path = npath.get_path()?;
        assert_eq!(path.get_type()?, AstNodeType::ShortestPath);
        let path = path.downcast_ref::<AstShortestPath>().unwrap();

        assert!(!path.is_single());

        let nodes: Vec<_> = path.elements().collect();
        assert_eq!(nodes[0].get_type()?, AstNodeType::NodePattern);
        let node = nodes[0].downcast_ref::<AstNodePattern>().unwrap();
        assert_eq!(node.get_identifier().unwrap().get_name(), "n");
        assert_eq!(node.nlabels(), 0);
        let labels: Vec<_> = node.labels().collect();
        assert_eq!(labels, vec![]);
        assert!(node.get_properties().is_none());

        assert_eq!(nodes[1].get_type()?, AstNodeType::RelPattern);
        let rel = nodes[1].downcast_ref::<AstRelPattern>().unwrap();
        assert_eq!(rel.get_direction(), RelDirection::OutBound);
        let id = rel.get_identifier();
        assert!(id.is_none());

        assert_eq!(rel.nreltypes(), 1);
        assert_eq!(
            rel.get_reltype(1).unwrap_err(),
            CypherParserError::OutOfRangeError(1)
        );
        let mut reltypes: Vec<_> = rel.reltypes().collect();
        let reltype = reltypes.pop().unwrap();
        assert_eq!(reltype.get_type()?, AstNodeType::Reltype);
        assert_eq!(reltype.get_name(), "Foo");

        assert!(rel.get_varlength().is_none());

        assert!(rel.get_properties().is_none());

        assert_eq!(nodes[2].get_type()?, AstNodeType::NodePattern);

        Ok(())
    }
}
