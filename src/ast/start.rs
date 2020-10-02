use super::*;

impl AstStart {
    pub fn npoints(&self) -> usize {
        unsafe { cypher::cypher_ast_start_npoints(self.as_ptr()) as usize }
    }

    pub fn get_point(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_start_get_point(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstQueryOption { ptr }.to_sub().unwrap(),
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn points<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.npoints(),
            func: &Self::get_point,
        }
    }

    pub fn get_predicate(&self) -> Option<Box<dyn AstNode>> {
        let ptr = unsafe { cypher::cypher_ast_start_get_predicate(self.as_ptr()) };
        // Bug, doesn't seem to return null when it should returns type 113 oddness
        (self.valid_ptr(ptr)).as_some_from(|| AstExpression { ptr }.to_sub().unwrap())
    }
}

impl AstStartPoint {
    // This is a super type
}

impl AstNodeIndexLookup {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_index_lookup_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("NodeIndexLookup.get_identifier"),
        )
    }

    pub fn get_index_name(&self) -> Result<AstIndexName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_index_lookup_get_index_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIndexName { ptr },
            CypherParserError::NullPtrError("NodeIndexLookup.get_index_name"),
        )
    }

    pub fn get_lookup(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        // string or parameter
        let ptr = unsafe { cypher::cypher_ast_node_index_lookup_get_lookup(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstRoot { ptr }.to_sub()?,
            CypherParserError::NullPtrError("NodeIndexLookup.get_lookup"),
        )
    }

    pub fn get_prop_name(&self) -> Result<AstPropName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_index_lookup_get_prop_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstPropName { ptr },
            CypherParserError::NullPtrError("NodeIndexLookup.get_prop_name"),
        )
    }
}

impl AstNodeIndexQuery {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_index_query_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("NodeIndexQuery.get_identifier"),
        )
    }

    pub fn get_index_name(&self) -> Result<AstIndexName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_index_query_get_index_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIndexName { ptr },
            CypherParserError::NullPtrError("NodeIndexQuery.get_index_name"),
        )
    }

    pub fn get_query(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        // string or parameter
        let ptr = unsafe { cypher::cypher_ast_node_index_query_get_query(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstRoot { ptr }.to_sub()?,
            CypherParserError::NullPtrError("NodeIndexQuery.get_query"),
        )
    }
}

impl AstNodeIdLookup {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_id_lookup_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("NodeIdLookup.get_identifier"),
        )
    }

    pub fn get_id(&self, idx: usize) -> Result<AstInteger, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_node_id_lookup_get_id(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr)
            .as_result(AstInteger { ptr }, CypherParserError::OutOfRangeError(idx))
    }

    pub fn nids(&self) -> usize {
        unsafe { cypher::cypher_ast_node_id_lookup_nids(self.as_ptr()) as usize }
    }

    pub fn ids<'a>(&'a self) -> AstNodeIter<'a, AstInteger, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nids(),
            func: &Self::get_id,
        }
    }
}

impl AstAllNodesScan {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_all_nodes_scan_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("AllNodesScan.get_identifier"),
        )
    }
}

impl AstRelIndexLookup {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_index_lookup_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("RelIndexLookup.get_identifier"),
        )
    }

    pub fn get_index_name(&self) -> Result<AstIndexName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_index_lookup_get_index_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIndexName { ptr },
            CypherParserError::NullPtrError("RelIndexLookup.get_index_name"),
        )
    }

    pub fn get_lookup(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_index_lookup_get_lookup(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstRoot { ptr }.to_sub()?,
            CypherParserError::NullPtrError("RelIndexLookup.get_prop_name"),
        )
    }

    pub fn get_prop_name(&self) -> Result<AstPropName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_index_lookup_get_prop_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstPropName { ptr },
            CypherParserError::NullPtrError("RelIndexLookup.get_prop_name"),
        )
    }
}

impl AstRelIndexQuery {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_index_query_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("RelIndexQuery.get_identifier"),
        )
    }

    pub fn get_index_name(&self) -> Result<AstIndexName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_index_query_get_index_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIndexName { ptr },
            CypherParserError::NullPtrError("RelIndexQuery.get_index_name"),
        )
    }

    pub fn get_query(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        // string or parameter
        let ptr = unsafe { cypher::cypher_ast_rel_index_query_get_query(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstRoot { ptr }.to_sub()?,
            CypherParserError::NullPtrError("RelIndexQuery.get_query"),
        )
    }
}

impl AstRelIdLookup {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_id_lookup_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("RelIdLookup.get_identifier"),
        )
    }

    pub fn get_id(&self, idx: usize) -> Result<AstInteger, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_rel_id_lookup_get_id(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr)
            .as_result(AstInteger { ptr }, CypherParserError::OutOfRangeError(idx))
    }

    pub fn nids(&self) -> usize {
        unsafe { cypher::cypher_ast_rel_id_lookup_nids(self.as_ptr()) as usize }
    }

    pub fn ids<'a>(&'a self) -> AstNodeIter<'a, AstInteger, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nids(),
            func: &Self::get_id,
        }
    }
}

impl AstAllRelsScan {
    // instance of AstStartPoint
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_all_rels_scan_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("AllRelsScan.get_identifier"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_node_index_lookup() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n=node:index(foo = 'bar');",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookup = start.get_point(0)?;
        assert_eq!(lookup.get_type()?, AstNodeType::NodeIndexLookup);
        let lookup = lookup.downcast_ref::<AstNodeIndexLookup>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        let index_name = lookup.get_index_name()?;
        assert_eq!(index_name.get_value(), "index");

        let prop_name = lookup.get_prop_name()?;
        assert_eq!(prop_name.get_value(), "foo");

        let s = lookup.get_lookup()?;
        assert_eq!(s.get_type()?, AstNodeType::String);
        let s = s.downcast_ref::<AstString>().unwrap();
        assert_eq!(s.get_value(), "bar");

        Ok(())
    }

    #[test]
    fn parse_node_index_query() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n=node:index('bar');",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookup = start.get_point(0)?;
        assert_eq!(lookup.get_type()?, AstNodeType::NodeIndexQuery);
        let lookup = lookup.downcast_ref::<AstNodeIndexQuery>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        let index_name = lookup.get_index_name()?;
        assert_eq!(index_name.get_value(), "index");

        let query = lookup.get_query()?;
        assert_eq!(query.get_type()?, AstNodeType::String);
        let query = query.downcast_ref::<AstString>().unwrap();
        assert_eq!(query.get_value(), "bar");

        Ok(())
    }

    #[test]
    fn parse_node_id_lookup() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n=node(65, 78, 3, 0) // find nodes\nRETURN n;",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookup = start.get_point(0)?;
        assert_eq!(lookup.get_type()?, AstNodeType::NodeIdLookup);
        let lookup = lookup.downcast_ref::<AstNodeIdLookup>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        assert_eq!(lookup.nids(), 4);

        let ids: Vec<_> = lookup.ids().collect();
        assert_eq!(ids[0].get_value()?, 65);
        assert_eq!(ids[1].get_value()?, 78);
        assert_eq!(ids[2].get_value()?, 3);
        assert_eq!(ids[3].get_value()?, 0);

        Ok(())
    }

    #[test]
    fn parse_all_node_scan() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n = node(*)\nRETURN /* all nodes */ n;",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookup = start.get_point(0)?;
        assert_eq!(lookup.get_type()?, AstNodeType::AllNodesScan);
        let lookup = lookup.downcast_ref::<AstAllNodesScan>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        Ok(())
    }

    #[test]
    fn parse_rel_index_lookup() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n=rel:index(foo = 'bar');",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookups: Vec<_> = start.points().collect();
        assert_eq!(lookups[0].get_type()?, AstNodeType::RelIndexLookup);
        let lookup = lookups[0].downcast_ref::<AstRelIndexLookup>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        let index_name = lookup.get_index_name()?;
        assert_eq!(index_name.get_value(), "index");

        let prop_name = lookup.get_prop_name()?;
        assert_eq!(prop_name.get_value(), "foo");

        let s = lookup.get_lookup()?;
        assert_eq!(s.get_type()?, AstNodeType::String);
        let s = s.downcast_ref::<AstString>().unwrap();
        assert_eq!(s.get_value(), "bar");

        Ok(())
    }

    #[test]
    fn parse_rel_index_query() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n=rel:index('bar');",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookups: Vec<_> = start.points().collect();
        assert_eq!(lookups[0].get_type()?, AstNodeType::RelIndexQuery);
        let lookup = lookups[0].downcast_ref::<AstRelIndexQuery>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        let index_name = lookup.get_index_name()?;
        assert_eq!(index_name.get_value(), "index");

        let query = lookup.get_query()?;
        assert_eq!(query.get_type()?, AstNodeType::String);
        let query = query.downcast_ref::<AstString>().unwrap();
        assert_eq!(query.get_value(), "bar");

        Ok(())
    }

    #[test]
    fn parse_rel_node_id() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n=rel(55, 72, 15, 0) // find nodes\nRETURN n;",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookups: Vec<_> = start.points().collect();
        assert_eq!(lookups[0].get_type()?, AstNodeType::RelIdLookup);
        let lookup = lookups[0].downcast_ref::<AstRelIdLookup>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        assert_eq!(lookup.nids(), 4);

        let ids: Vec<_> = lookup.ids().collect();
        assert_eq!(ids[0].get_value()?, 55);
        assert_eq!(ids[1].get_value()?, 72);
        assert_eq!(ids[2].get_value()?, 15);
        assert_eq!(ids[3].get_value()?, 0);

        Ok(())
    }

    #[test]
    fn parse_all_rels_scan() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n = rel(*)\nRETURN /* all rels */ n;",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        assert!(start.get_predicate().is_none());
        assert_eq!(start.npoints(), 1);

        assert!(start.get_point(1).is_err());
        let lookups: Vec<_> = start.points().collect();
        assert_eq!(lookups[0].get_type()?, AstNodeType::AllRelsScan);
        let lookup = lookups[0].downcast_ref::<AstAllRelsScan>().unwrap();

        let id = lookup.get_identifier()?;
        assert_eq!(id.get_name(), "n");

        Ok(())
    }

    #[test]
    fn parse_start_with_predicate() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "START n = node(*) /* predicate */ WHERE n.foo > 1 RETURN n;",
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
        assert_eq!(clause.get_type()?, AstNodeType::Start);

        let start: &AstStart = clause.downcast_ref().unwrap();
        let predicate = start.get_predicate();
        assert!(predicate.is_some());
        let predicate = predicate.unwrap();
        assert!(predicate.instance_of(AstNodeType::Expression));
        assert_eq!(predicate.get_type()?, AstNodeType::Comparison);

        let comparison = predicate.downcast_ref::<AstComparison>().unwrap();

        assert_eq!(comparison.get_length(), 1);
        assert_eq!(comparison.get_operator(0)?, Operator::Gt);
        assert_eq!(
            comparison.get_argument(0)?.get_type()?,
            AstNodeType::PropertyOperator
        );
        assert_eq!(
            comparison.get_argument(1)?.get_type()?,
            AstNodeType::Integer
        );

        Ok(())
    }
}
