use super::*;

impl AstUsingPeriodicCommit {
    pub fn get_limit(&self) -> Option<AstInteger> {
        let ptr = unsafe { cypher::cypher_ast_using_periodic_commit_get_limit(self.as_ptr()) };
        self.valid_ptr(ptr).as_some(AstInteger { ptr })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOption, ParseResult};

    #[test]
    fn parse_query_with_periodic_commit_option() -> Result<(), CypherParserError> {
        let result = ParseResult::parse(
            "USING PERIODIC COMMIT 500 CREATE (n);",
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

        let body = body.downcast_ref::<AstQuery>().unwrap();
        assert_eq!(body.noptions(), 1);

        let mut options: Vec<_> = body.options().collect();
        let option = options.pop().unwrap();
        assert_eq!(option.get_type()?, AstNodeType::UsingPeriodicCommit);

        let option = option.downcast_ref::<AstUsingPeriodicCommit>().unwrap();
        assert_eq!(option.get_limit().unwrap().get_value()?, 500);

        Ok(())
    }
}
