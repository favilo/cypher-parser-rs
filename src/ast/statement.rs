use super::*;

impl AstStatement {
    pub fn noptions(&self) -> usize {
        unsafe { cypher::cypher_ast_statement_noptions(self.as_ptr()) as usize }
    }

    pub fn get_option(&self, idx: usize) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_statement_get_option(self.as_ptr(), idx as u32) };
        self.valid_ptr(ptr).as_result(
            AstStatementOption { ptr }.to_sub()?,
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

    pub fn get_body(&self) -> Result<Box<dyn AstNode>, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_statement_get_body(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstRoot { ptr }.to_sub()?,
            CypherParserError::NullPtrError("Statement.get_body"),
        )
    }
}

impl AstCypherOption {
    pub fn get_version(&self) -> Option<AstString> {
        let ptr = unsafe { cypher::cypher_ast_cypher_option_get_version(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstString { ptr })
    }

    pub fn nparams(&self) -> usize {
        unsafe { cypher::cypher_ast_cypher_option_nparams(self.as_ptr()) as usize }
    }

    pub fn get_param(&self, idx: usize) -> Result<AstCypherOptionParam, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_cypher_option_get_param(self.as_ptr(), idx as _) };
        self.valid_ptr(ptr).as_result(
            AstCypherOptionParam { ptr },
            CypherParserError::OutOfRangeError(idx),
        )
    }

    pub fn params<'a>(&'a self) -> AstNodeIter<'a, AstCypherOptionParam, Self> {
        AstNodeIter {
            obj: self,
            idx: 0,
            max: self.nparams(),
            func: &Self::get_param,
        }
    }
}

impl AstCypherOptionParam {
    pub fn get_name(&self) -> Result<AstString, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_cypher_option_param_get_name(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstString { ptr },
            CypherParserError::NullPtrError("CypherOptionParam.get_name"),
        )
    }

    pub fn get_value(&self) -> Result<AstString, CypherParserError> {
        let ptr = unsafe { cypher::cypher_ast_cypher_option_param_get_value(self.as_ptr()) };
        self.valid_ptr(ptr).as_result(
            AstString { ptr },
            CypherParserError::NullPtrError("CypherOptionParam.get_value"),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_statement_with_cypher_option() -> Result<(), CypherParserError> {
        let result =
            ParseResult::parse("CYPHER RETURN 1;", None, None, ParseOption::Default.into())?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 2);

        assert_eq!(statement.noptions(), 1);
        let mut options: Vec<_> = statement.options().collect();
        let option = options.pop().unwrap();
        assert!(option.instance_of(AstNodeType::StatementOption));
        assert_eq!(option.get_type()?, AstNodeType::CypherOption);
        let option = option.downcast_ref::<AstCypherOption>().unwrap();

        assert!(option.get_version().is_none());
        assert_eq!(option.nparams(), 0);
        assert!(option.get_param(0).is_err());

        Ok(())
    }

    #[test]
    fn parse_statement_with_cypher_option_containing_version_and_params(
    ) -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "CYPHER 2.3 runtime=fast planner=slow RETURN 1;",
            None,
            None,
            ParseOption::Default.into(),
        )?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 2);

        assert_eq!(statement.noptions(), 1);
        let option = statement.get_option(0)?;
        assert!(option.instance_of(AstNodeType::StatementOption));
        assert_eq!(option.get_type()?, AstNodeType::CypherOption);
        let option = option.downcast_ref::<AstCypherOption>().unwrap();

        let version = option.get_version().unwrap();
        assert_eq!(version.get_value(), "2.3");
        assert_eq!(option.nparams(), 2);
        let param = option.get_param(0)?;
        assert_eq!(param.get_name().unwrap().get_value(), "runtime");
        assert_eq!(param.get_value().unwrap().get_value(), "fast");
        let param = option.get_param(1)?;
        assert_eq!(param.get_name().unwrap().get_value(), "planner");
        assert_eq!(param.get_value().unwrap().get_value(), "slow");

        Ok(())
    }

    #[test]
    fn parse_statement_with_explain_option() -> Result<(), CypherParserError> {
        let result =
            ParseResult::parse("EXPLAIN RETURN 1;", None, None, ParseOption::Default.into())?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 2);

        assert_eq!(statement.noptions(), 1);
        let option = statement.get_option(0)?;
        assert!(option.instance_of(AstNodeType::StatementOption));
        assert_eq!(option.get_type()?, AstNodeType::ExplainOption);

        Ok(())
    }

    #[test]
    fn parse_statement_with_profile_option() -> Result<(), CypherParserError> {
        let result =
            ParseResult::parse("PROFILE RETURN 1;", None, None, ParseOption::Default.into())?;

        let statement = result.get_directive(0)?;
        let statement = statement.downcast_ref::<AstStatement>().unwrap();
        assert_eq!(statement.nchildren(), 2);

        assert_eq!(statement.noptions(), 1);
        let option = statement.get_option(0)?;
        for o in statement.options() {
            assert_eq!(option.get_type()?, o.get_type()?);
        }
        assert!(option.instance_of(AstNodeType::StatementOption));
        assert_eq!(option.get_type()?, AstNodeType::ProfileOption);

        Ok(())
    }
}
