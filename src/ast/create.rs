use super::*;

impl AstCreate {
    pub fn is_unique(&self) -> bool {
        unsafe { cypher::cypher_ast_create_is_unique(self.as_ptr()) }
    }

    pub fn get_pattern(&self) -> Option<AstPattern> {
        let ptr = unsafe { cypher::cypher_ast_create_get_pattern(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstPattern { ptr })
    }
}

impl AstCreateNodePropIndex {
    pub fn get_label(&self) -> Result<AstLabel, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_create_node_prop_index_get_label(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstLabel { ptr },
            CypherParserError::NullPtrError("CreateNodePropIndex.get_label"),
        )
    }

    pub fn get_prop_name(&self) -> Result<AstPropName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_create_node_prop_index_get_prop_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstPropName { ptr },
            CypherParserError::NullPtrError("CreateNodePropIndex.get_prop_name"),
        )
    }
}

impl AstDropNodePropIndex {
    pub fn get_label(&self) -> Result<AstLabel, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_drop_node_prop_index_get_label(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstLabel { ptr },
            CypherParserError::NullPtrError("DropNodePropIndex.get_label"),
        )
    }

    pub fn get_prop_name(&self) -> Result<AstPropName, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_drop_node_prop_index_get_prop_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstPropName { ptr },
            CypherParserError::NullPtrError("DropNodePropIndex.get_prop_name"),
        )
    }
}

impl AstCreateNodePropConstraint {
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_create_node_prop_constraint_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("CreateNodePropConstraint.get_identifier"),
        )
    }

    pub fn get_label(&self) -> Result<AstLabel, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_create_node_prop_constraint_get_label(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstLabel { ptr },
            CypherParserError::NullPtrError("CreateNodePropConstraint.get_identifier"),
        )
    }

    pub fn is_unique(&self) -> bool {
        unsafe { cypher::cypher_ast_create_node_prop_constraint_is_unique(self.as_ptr()) }
    }

    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_create_node_prop_constraint_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstExpression { ptr }.to_sub()?,
            CypherParserError::NullPtrError("CreateNodePropConstraint.get_expression"),
        )
    }
}

impl AstDropNodePropConstraint {
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_drop_node_prop_constraint_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("DropNodePropConstraint.get_identifier"),
        )
    }

    pub fn get_label(&self) -> Result<AstLabel, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_drop_node_prop_constraint_get_label(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstLabel { ptr },
            CypherParserError::NullPtrError("DropNodePropConstraint.get_identifier"),
        )
    }

    pub fn is_unique(&self) -> bool {
        unsafe { cypher::cypher_ast_drop_node_prop_constraint_is_unique(self.as_ptr()) }
    }

    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_drop_node_prop_constraint_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstExpression { ptr }.to_sub()?,
            CypherParserError::NullPtrError("DropNodePropConstraint.get_expression"),
        )
    }
}

impl AstCreateRelPropConstraint {
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_create_rel_prop_constraint_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("CreateRelPropConstraint.get_identifier"),
        )
    }

    pub fn get_reltype(&self) -> Result<AstReltype, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_create_rel_prop_constraint_get_reltype(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstReltype { ptr },
            CypherParserError::NullPtrError("CreateRelPropConstraint.get_identifier"),
        )
    }

    pub fn is_unique(&self) -> bool {
        unsafe { cypher::cypher_ast_create_rel_prop_constraint_is_unique(self.as_ptr()) }
    }

    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_create_rel_prop_constraint_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstExpression { ptr }.to_sub()?,
            CypherParserError::NullPtrError("CreateRelPropConstraint.get_expression"),
        )
    }
}

impl AstDropRelPropConstraint {
    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_drop_rel_prop_constraint_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("DropRelPropConstraint.get_identifier"),
        )
    }

    pub fn get_reltype(&self) -> Result<AstReltype, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_drop_rel_prop_constraint_get_reltype(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstReltype { ptr },
            CypherParserError::NullPtrError("DropRelPropConstraint.get_identifier"),
        )
    }

    pub fn is_unique(&self) -> bool {
        unsafe { cypher::cypher_ast_drop_rel_prop_constraint_is_unique(self.as_ptr()) }
    }

    pub fn get_expression(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr =
            unsafe { cypher::cypher_ast_drop_rel_prop_constraint_get_expression(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstExpression { ptr }.to_sub()?,
            CypherParserError::NullPtrError("DropRelPropConstraint.get_expression"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_simple_create() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "CREATE (n)-[:KNOWS]->(f);",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let ast = result.get_directive(0)?;
        assert_eq!(ast.get_type()?, AstNodeType::Statement);
        let ast = ast.downcast_ref::<AstStatement>().unwrap();
        let query = ast.get_body()?;
        assert_eq!(query.get_type()?, AstNodeType::Query);
        let query = query.downcast_ref::<AstQuery>().unwrap();

        let create = query.get_clause(0)?;
        assert_eq!(create.get_type()?, AstNodeType::Create);
        let create = create.downcast_ref::<AstCreate>().unwrap();
        assert!(!create.is_unique());

        let pattern = create.get_pattern().unwrap();
        assert_eq!(pattern.get_type()?, AstNodeType::Pattern);
        assert_eq!(pattern.npaths(), 1);

        Ok(())
    }

    #[test]
    fn parse_create_unique_node_prop_constraint() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "CREATE CONSTRAINT ON (f:Foo) ASSERT f.bar IS UNIQUE;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 1);

        assert_eq!(statement.noptions(), 0);
        assert!(statement.get_option(0).is_err());

        let body = statement.get_body()?;
        assert_eq!(body.get_type()?, AstNodeType::CreateNodePropConstraint);

        let range = body.range();
        assert_eq!(range.start().offset(), 0);
        assert_eq!(range.end().offset(), 51);

        let body = body.downcast_ref::<AstCreateNodePropConstraint>().unwrap();
        assert_eq!(body.get_identifier()?.get_name(), "f");
        assert_eq!(body.get_label()?.get_name(), "Foo");

        let expression = body.get_expression()?;
        assert!(expression.instance_of(AstNodeType::Expression));
        assert_eq!(expression.get_type()?, AstNodeType::PropertyOperator);

        let expression = expression.downcast_ref::<AstPropertyOperator>().unwrap();
        let expr = expression.get_expression()?;

        assert!(expr.instance_of(AstNodeType::Expression));
        assert_eq!(expr.get_type()?, AstNodeType::Identifier);

        assert_eq!(
            expr.downcast_ref::<AstIdentifier>().unwrap().get_name(),
            "f"
        );
        let prop_name = expression.get_prop_name()?;
        assert_eq!(prop_name.get_value(), "bar");

        assert!(body.is_unique());

        Ok(())
    }
}
