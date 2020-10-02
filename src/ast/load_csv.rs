use super::*;

impl AstLoadCsv {
    pub fn has_with_headers(&self) -> bool {
        unsafe { cypher::cypher_ast_load_csv_has_with_headers(self.as_ptr()) }
    }

    pub fn get_url(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_load_csv_get_url(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstExpression { ptr }.to_sub()?,
            CypherParserError::NullPtrError("LoadCsv.get_url"),
        )
    }

    pub fn get_identifier(&self) -> Result<AstIdentifier, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_load_csv_get_identifier(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstIdentifier { ptr },
            CypherParserError::NullPtrError("LoadCsv.get_url"),
        )
    }

    pub fn get_field_terminator(&self) -> Option<AstString> {
        let ptr = unsafe { cypher::cypher_ast_load_csv_get_field_terminator(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstString { ptr })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_load_csv() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "LOAD CSV FROM 'file:///movies.csv' AS m RETURN m;",
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
        assert_eq!(body.get_type()?, AstNodeType::Query);

        let query = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(query.noptions(), 0);

        let clause = query.get_clause(0)?;
        assert_eq!(clause.get_type()?, AstNodeType::LoadCsv);

        let clause = clause.downcast_ref::<AstLoadCsv>().unwrap();
        assert!(!clause.has_with_headers());

        let url = clause.get_url()?;
        assert_eq!(url.get_type()?, AstNodeType::String);
        let url = url.downcast_ref::<AstString>().unwrap();
        assert_eq!(url.get_value(), "file:///movies.csv");
        let id = clause.get_identifier()?;
        assert_eq!(id.get_name(), "m");

        assert!(clause.get_field_terminator().is_none());

        Ok(())
    }
}
