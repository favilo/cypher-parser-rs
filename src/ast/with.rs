use super::*;

impl AstWith {
    pub fn is_distinct(&self) -> bool {
        unsafe { cypher::cypher_ast_with_is_distinct(self.as_ptr()) }
    }

    pub fn has_include_existing(&self) -> bool {
        unsafe { cypher::cypher_ast_with_has_include_existing(self.as_ptr()) }
    }

    pub fn nprojections(&self) -> usize {
        unsafe { cypher::cypher_ast_with_nprojections(self.as_ptr()) as usize }
    }

    pub fn get_projection(&self, idx: usize) -> Result<AstProjection, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_with_get_projection(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstProjection { ptr },
            || CypherParserError::OutOfRangeError(idx),
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

    pub fn get_limit(&self) -> Option<AstInteger> {
        let ptr = unsafe { cypher::cypher_ast_with_get_limit(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstInteger { ptr })
    }

    pub fn get_order_by(&self) -> Option<AstOrderBy> {
        let ptr = unsafe { cypher::cypher_ast_with_get_order_by(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstOrderBy { ptr })
    }

    pub fn get_skip(&self) -> Option<AstInteger> {
        let ptr = unsafe { cypher::cypher_ast_with_get_skip(self.as_ptr()) };
        self.valid_ptr(ptr).as_some_from(|| AstInteger { ptr })
    }

    pub fn get_predicate(&self) -> Option<Box<dyn AstNode>> {
        let ptr = unsafe { cypher::cypher_ast_with_get_predicate(self.as_ptr()) };
        self.valid_ptr(ptr)
            .as_some_from(|| AstExpression { ptr }.to_sub().unwrap())
    }
}

impl AstOrderBy {
    pub fn nitems(&self) -> usize {
        unsafe { cypher::cypher_ast_order_by_nitems(self.as_ptr()) as usize }
    }

    pub fn get_item(&self, idx: usize) -> Result<AstSortItem, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_order_by_get_item(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result_from(
            || AstSortItem { ptr },
            || CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn items<'a>(&'a self) -> AstNodeIter<'a, AstSortItem, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nitems(),
            func: &Self::get_item,
        }
    }
}

impl AstSortItem {
    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_sort_item_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result_from(
            || AstExpression { ptr }.to_sub().unwrap(),
            || CypherParserError::NullPtrError("SortItem::get_expression"),
        )
    }

    pub fn is_ascending(&self) -> bool {
        unsafe { cypher::cypher_ast_sort_item_is_ascending(self.as_ptr()) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_simple_with() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "WITH 1 AS x, 'bar' AS y RETURN x, y",
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
        assert_eq!(clause.get_type()?, AstNodeType::With);

        let with: &AstWith = clause.downcast_ref().unwrap();
        assert!(!with.is_distinct());
        assert!(!with.has_include_existing());

        assert_eq!(with.nprojections(), 2);
        assert_eq!(
            with.get_projection(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );

        let projections: Vec<_> = with.projections().collect();
        assert_eq!(
            projections[0].get_expression()?.get_type()?,
            AstNodeType::Integer
        );
        assert_eq!(
            projections[0]
                .get_expression()?
                .downcast_ref::<AstInteger>()
                .unwrap()
                .get_value()?,
            1
        );
        assert_eq!(
            projections[0].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[0].get_alias().unwrap().get_name(), "x");

        assert_eq!(
            projections[1].get_expression()?.get_type()?,
            AstNodeType::String
        );
        assert_eq!(
            projections[1]
                .get_expression()?
                .downcast_ref::<AstString>()
                .unwrap()
                .get_value(),
            "bar"
        );
        assert_eq!(
            projections[1].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[1].get_alias().unwrap().get_name(), "y");

        assert!(with.get_order_by().is_none());
        assert!(with.get_skip().is_none());
        assert!(with.get_limit().is_none());
        assert!(with.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_distinct_with() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "WITH DISTINCT 1 AS x, 'bar' AS y RETURN x, y",
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
        assert_eq!(clause.get_type()?, AstNodeType::With);

        let with: &AstWith = clause.downcast_ref().unwrap();
        assert!(with.is_distinct());
        assert!(!with.has_include_existing());

        assert_eq!(with.nprojections(), 2);
        assert_eq!(
            with.get_projection(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );

        let projections: Vec<_> = with.projections().collect();
        assert_eq!(
            projections[0].get_expression()?.get_type()?,
            AstNodeType::Integer
        );
        assert_eq!(
            projections[0]
                .get_expression()?
                .downcast_ref::<AstInteger>()
                .unwrap()
                .get_value()?,
            1
        );
        assert_eq!(
            projections[0].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[0].get_alias().unwrap().get_name(), "x");

        assert_eq!(
            projections[1].get_expression()?.get_type()?,
            AstNodeType::String
        );
        assert_eq!(
            projections[1]
                .get_expression()?
                .downcast_ref::<AstString>()
                .unwrap()
                .get_value(),
            "bar"
        );
        assert_eq!(
            projections[1].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[1].get_alias().unwrap().get_name(), "y");

        assert!(with.get_order_by().is_none());
        assert!(with.get_skip().is_none());
        assert!(with.get_limit().is_none());
        assert!(with.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_with_including_existing() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "WITH *, 1 AS x, 'bar' AS y RETURN x, y",
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
        assert_eq!(clause.get_type()?, AstNodeType::With);

        let with: &AstWith = clause.downcast_ref().unwrap();
        assert!(!with.is_distinct());
        assert!(with.has_include_existing());

        assert_eq!(with.nprojections(), 2);
        assert_eq!(
            with.get_projection(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );

        let projections: Vec<_> = with.projections().collect();
        assert_eq!(
            projections[0].get_expression()?.get_type()?,
            AstNodeType::Integer
        );
        assert_eq!(
            projections[0]
                .get_expression()?
                .downcast_ref::<AstInteger>()
                .unwrap()
                .get_value()?,
            1
        );
        assert_eq!(
            projections[0].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[0].get_alias().unwrap().get_name(), "x");

        assert_eq!(
            projections[1].get_expression()?.get_type()?,
            AstNodeType::String
        );
        assert_eq!(
            projections[1]
                .get_expression()?
                .downcast_ref::<AstString>()
                .unwrap()
                .get_value(),
            "bar"
        );
        assert_eq!(
            projections[1].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[1].get_alias().unwrap().get_name(), "y");

        assert!(with.get_order_by().is_none());
        assert!(with.get_skip().is_none());
        assert!(with.get_limit().is_none());
        assert!(with.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_with_and_order_by() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "WITH 1 AS x, 'bar' AS y ORDER BY x DESC, y ASC, z.prop + 10",
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
        assert_eq!(clause.get_type()?, AstNodeType::With);

        let with: &AstWith = clause.downcast_ref().unwrap();
        assert!(!with.is_distinct());
        assert!(!with.has_include_existing());

        assert_eq!(with.nprojections(), 2);
        assert_eq!(
            with.get_projection(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );

        let projections: Vec<_> = with.projections().collect();
        assert_eq!(
            projections[0].get_expression()?.get_type()?,
            AstNodeType::Integer
        );
        assert_eq!(
            projections[0]
                .get_expression()?
                .downcast_ref::<AstInteger>()
                .unwrap()
                .get_value()?,
            1
        );
        assert_eq!(
            projections[0].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[0].get_alias().unwrap().get_name(), "x");

        assert_eq!(
            projections[1].get_expression()?.get_type()?,
            AstNodeType::String
        );
        assert_eq!(
            projections[1]
                .get_expression()?
                .downcast_ref::<AstString>()
                .unwrap()
                .get_value(),
            "bar"
        );
        assert_eq!(
            projections[1].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[1].get_alias().unwrap().get_name(), "y");

        let order_by = with.get_order_by().unwrap();
        assert_eq!(order_by.nitems(), 3);
        assert_eq!(
            order_by.get_item(3).unwrap_err(),
            CypherParserError::OutOfRangeError(3)
        );

        let items: Vec<_> = order_by.items().collect();

        assert_eq!(items[0].get_type()?, AstNodeType::SortItem);
        assert_eq!(
            items[0].get_expression()?.get_type()?,
            AstNodeType::Identifier
        );
        assert!(!items[0].is_ascending());

        assert_eq!(items[1].get_type()?, AstNodeType::SortItem);
        assert_eq!(
            items[1].get_expression()?.get_type()?,
            AstNodeType::Identifier
        );
        assert!(items[1].is_ascending());

        assert_eq!(items[2].get_type()?, AstNodeType::SortItem);
        assert_eq!(
            items[2].get_expression()?.get_type()?,
            AstNodeType::BinaryOperator
        );
        assert!(items[2].is_ascending());

        assert!(with.get_skip().is_none());
        assert!(with.get_limit().is_none());
        assert!(with.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_with_and_skip() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "WITH *, 1 AS x, 'bar' AS y SKIP 10",
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
        assert_eq!(clause.get_type()?, AstNodeType::With);

        let with: &AstWith = clause.downcast_ref().unwrap();
        assert!(!with.is_distinct());
        assert!(with.has_include_existing());

        assert_eq!(with.nprojections(), 2);
        assert_eq!(
            with.get_projection(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );

        let projections: Vec<_> = with.projections().collect();
        assert_eq!(
            projections[0].get_expression()?.get_type()?,
            AstNodeType::Integer
        );
        assert_eq!(
            projections[0]
                .get_expression()?
                .downcast_ref::<AstInteger>()
                .unwrap()
                .get_value()?,
            1
        );
        assert_eq!(
            projections[0].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[0].get_alias().unwrap().get_name(), "x");

        assert_eq!(
            projections[1].get_expression()?.get_type()?,
            AstNodeType::String
        );
        assert_eq!(
            projections[1]
                .get_expression()?
                .downcast_ref::<AstString>()
                .unwrap()
                .get_value(),
            "bar"
        );
        assert_eq!(
            projections[1].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[1].get_alias().unwrap().get_name(), "y");

        assert!(with.get_order_by().is_none());

        let skip = with.get_skip().unwrap();
        assert_eq!(skip.get_value()?, 10);

        assert!(with.get_limit().is_none());
        assert!(with.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_with_and_skip_limit() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "WITH *, 1 AS x, 'bar' AS y SKIP 10 LIMIT 5",
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
        assert_eq!(clause.get_type()?, AstNodeType::With);

        let with: &AstWith = clause.downcast_ref().unwrap();
        assert!(!with.is_distinct());
        assert!(with.has_include_existing());

        assert_eq!(with.nprojections(), 2);
        assert_eq!(
            with.get_projection(2).unwrap_err(),
            CypherParserError::OutOfRangeError(2)
        );

        let projections: Vec<_> = with.projections().collect();
        assert_eq!(
            projections[0].get_expression()?.get_type()?,
            AstNodeType::Integer
        );
        assert_eq!(
            projections[0]
                .get_expression()?
                .downcast_ref::<AstInteger>()
                .unwrap()
                .get_value()?,
            1
        );
        assert_eq!(
            projections[0].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[0].get_alias().unwrap().get_name(), "x");

        assert_eq!(
            projections[1].get_expression()?.get_type()?,
            AstNodeType::String
        );
        assert_eq!(
            projections[1]
                .get_expression()?
                .downcast_ref::<AstString>()
                .unwrap()
                .get_value(),
            "bar"
        );
        assert_eq!(
            projections[1].get_alias().unwrap().get_type()?,
            AstNodeType::Identifier
        );
        assert_eq!(projections[1].get_alias().unwrap().get_name(), "y");

        assert!(with.get_order_by().is_none());

        let skip = with.get_skip().unwrap();
        assert_eq!(skip.get_value()?, 10);

        let limit = with.get_limit().unwrap();
        assert_eq!(limit.get_value()?, 5);
        assert!(with.get_predicate().is_none());

        Ok(())
    }

    #[test]
    fn parse_with_and_predicate() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "WITH * WHERE n.foo > 10",
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
        assert_eq!(clause.get_type()?, AstNodeType::With);

        let with: &AstWith = clause.downcast_ref().unwrap();
        assert!(!with.is_distinct());
        assert!(with.has_include_existing());

        assert_eq!(with.nprojections(), 0);
        assert_eq!(
            with.get_projection(0).unwrap_err(),
            CypherParserError::OutOfRangeError(0)
        );

        let projections: Vec<_> = with.projections().collect();
        assert_eq!(projections, []);

        assert!(with.get_order_by().is_none());

        assert!(with.get_skip().is_none());
        assert!(with.get_limit().is_none());
        let predicate = with.get_predicate().unwrap();
        assert_eq!(predicate.get_type()?, AstNodeType::Comparison);
        let predicate = predicate.downcast_ref::<AstComparison>().unwrap();
        assert_eq!(predicate.get_length(), 1);
        assert_eq!(predicate.get_operator(0)?, Operator::Gt);
        assert_eq!(
            predicate.get_argument(0)?.get_type()?,
            AstNodeType::PropertyOperator
        );

        Ok(())
    }
}
