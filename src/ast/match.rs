use super::*;

impl AstMatch {
    pub fn get_pattern(&self) -> Option<AstPattern> {
        let ptr = unsafe { cypher::cypher_ast_match_get_pattern(self.as_ptr()) };

        self.valid_ptr(ptr).as_some(AstPattern { ptr })
    }

    pub fn is_optional(&self) -> bool {
        unsafe { cypher::cypher_ast_match_is_optional(self.as_ptr()) }
    }

    pub fn nhints(&self) -> usize {
        unsafe { cypher::cypher_ast_match_nhints(self.as_ptr()) as usize }
    }

    pub fn get_hint(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_match_get_hint(self.as_ptr(), idx as u32) };

        self.valid_ptr(ptr).as_result_from(
            || AstMatchHint { ptr }.to_sub().unwrap(),
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn hints<'a>(&'a self) -> AstNodeIter<'a, Box<dyn AstNode>, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nhints(),
            func: &Self::get_hint,
        }
    }

    pub fn get_predicate(&self) -> Option<Box<dyn AstNode>> {
        let ptr = unsafe { cypher::cypher_ast_match_get_predicate(self.as_ptr()) };

        self.valid_ptr(ptr)
            .as_some_from(|| AstExpression { ptr }.to_sub().unwrap())
    }
}

impl AstLabelsOperator {
    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_labels_operator_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstExpression { ptr }.to_sub().unwrap(),
            || CypherParserError::NullPtrError("LabelsOperator::get_expression"),
        )
    }

    pub fn nlabels(&self) -> usize {
        unsafe { cypher::cypher_ast_labels_operator_nlabels(self.as_ptr()) as usize }
    }

    pub fn get_label(&self, idx: usize) -> Result<AstLabel, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_labels_operator_get_label(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstLabel { ptr },
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn labels<'a>(&'a self) -> AstNodeIter<'a, AstLabel, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nlabels(),
            func: &Self::get_label,
        }
    }
}

impl AstUsingIndex {
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_using_index_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstIdentifier { ptr },
            || CypherParserError::NullPtrError("UsingIndex::get_identifier"),
        )
    }

    pub fn get_label(&self) -> Result<AstLabel, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_using_index_get_label(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstLabel { ptr },
            || CypherParserError::NullPtrError("UsingIndex::get_label"),
        )
    }

    pub fn get_prop_name(&self) -> Result<AstPropName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_using_index_get_prop_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstPropName { ptr },
            || CypherParserError::NullPtrError("UsingIndex::get_prop_name"),
        )
    }
}

impl AstUsingJoin {
    pub fn get_identifier(&self, idx: usize) -> Result<AstIdentifier, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_using_join_get_identifier(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstIdentifier { ptr },
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn nidentifiers(&self) -> usize {
        unsafe { cypher::cypher_ast_using_join_nidentifiers(self.as_ptr()) as usize }
    }

    pub fn identifiers<'a>(&'a self) -> AstNodeIter<'a, AstIdentifier, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nidentifiers(),
            func: &Self::get_identifier,
        }
    }
}

impl AstUsingScan {
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_using_scan_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstIdentifier { ptr },
            || CypherParserError::NullPtrError("UsingScan::get_identifier"),
        )
    }

    pub fn get_label(&self) -> Result<AstLabel, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_using_scan_get_label(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstLabel { ptr },
            || CypherParserError::NullPtrError("UsingScan::get_label"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_simple_match() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n)-[:KNOWS]->(f) RETURN f;",
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

        let r#match: &AstMatch = clause.downcast_ref().unwrap();
        assert!(!r#match.is_optional());

        let pattern = r#match.get_pattern().unwrap();
        assert_eq!(pattern.npaths(), 1);

        assert_eq!(r#match.nhints(), 0);
        assert!(r#match.get_hint(0).is_err());
        assert!(r#match.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_simple_optional_match() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "OPTIONAL MATCH (n) RETURN n;",
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

        let r#match: &AstMatch = clause.downcast_ref().unwrap();
        assert!(r#match.is_optional());

        let pattern = r#match.get_pattern().unwrap();
        assert_eq!(pattern.npaths(), 1);

        assert_eq!(r#match.nhints(), 0);
        assert!(r#match.get_hint(0).is_err());
        assert!(r#match.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_match_with_predicate() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n) WHERE n:Foo RETURN n;",
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

        let r#match: &AstMatch = clause.downcast_ref().unwrap();
        assert!(!r#match.is_optional());

        let pattern = r#match.get_pattern().unwrap();
        assert_eq!(pattern.npaths(), 1);

        assert_eq!(r#match.nhints(), 0);
        assert!(r#match.get_hint(0).is_err());

        let predicate = r#match.get_predicate().unwrap();
        assert_eq!(predicate.get_type()?, AstNodeType::LabelsOperator);

        let labels_operator = predicate.downcast_ref::<AstLabelsOperator>().unwrap();
        let id = labels_operator.get_expression()?;
        assert_eq!(id.get_type()?, AstNodeType::Identifier);

        let id = id.downcast_ref::<AstIdentifier>().unwrap();
        assert_eq!(id.get_name(), "n");

        assert_eq!(labels_operator.nlabels(), 1);
        let labels: Vec<_> = labels_operator.labels().collect();
        assert_eq!(labels[0].get_name(), "Foo");

        Ok(())
    }

    #[test]
    fn parse_match_with_using_index_hint() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n:Foo) USING INDEX n:Foo(bar) RETURN n;",
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

        let r#match: &AstMatch = clause.downcast_ref().unwrap();
        assert!(!r#match.is_optional());

        let pattern = r#match.get_pattern().unwrap();
        assert_eq!(pattern.npaths(), 1);

        assert_eq!(r#match.nhints(), 1);
        assert!(r#match.get_hint(1).is_err());
        let hints: Vec<_> = r#match.hints().collect();
        assert_eq!(hints[0].get_type()?, AstNodeType::UsingIndex);

        assert!(r#match.get_predicate().is_none());

        let hint = hints[0].downcast_ref::<AstUsingIndex>().unwrap();
        assert_eq!(hint.get_identifier()?.get_name(), "n");
        assert_eq!(hint.get_label()?.get_type()?, AstNodeType::Label);
        assert_eq!(hint.get_label()?.get_name(), "Foo");
        assert_eq!(hint.get_prop_name()?.get_type()?, AstNodeType::PropName);
        assert_eq!(hint.get_prop_name()?.get_value(), "bar");

        Ok(())
    }

    #[test]
    fn parse_match_with_using_join_hint() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n), (m) USING JOIN ON n, m RETURN n;",
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

        let r#match: &AstMatch = clause.downcast_ref().unwrap();
        assert!(!r#match.is_optional());

        let pattern = r#match.get_pattern().unwrap();
        assert_eq!(pattern.npaths(), 2);

        assert_eq!(r#match.nhints(), 1);
        assert!(r#match.get_hint(1).is_err());
        let hint = r#match.get_hint(0)?;
        assert_eq!(hint.get_type()?, AstNodeType::UsingJoin);

        assert!(r#match.get_predicate().is_none());

        let hint = hint.downcast_ref::<AstUsingJoin>().unwrap();
        let ids: Vec<_> = hint.identifiers().collect();
        assert_eq!(ids.len(), 2);
        assert_eq!(ids[0].get_name(), "n");
        assert_eq!(ids[1].get_name(), "m");

        Ok(())
    }

    #[test]
    fn parse_match_with_using_scan_hint() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "MATCH (n:Foo) USING SCAN n:Foo RETURN n;",
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

        let r#match: &AstMatch = clause.downcast_ref().unwrap();
        assert!(!r#match.is_optional());

        let pattern = r#match.get_pattern().unwrap();
        assert_eq!(pattern.npaths(), 1);

        assert_eq!(r#match.nhints(), 1);
        assert!(r#match.get_hint(1).is_err());
        let hint = r#match.get_hint(0)?;
        assert_eq!(hint.get_type()?, AstNodeType::UsingScan);

        assert!(r#match.get_predicate().is_none());

        let hint = hint.downcast_ref::<AstUsingScan>().unwrap();
        assert_eq!(hint.get_identifier()?.get_name(), "n");
        assert_eq!(hint.get_label()?.get_name(), "Foo");

        Ok(())
    }
}
