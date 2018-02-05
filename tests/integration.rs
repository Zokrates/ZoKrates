extern crate assert_cli;

#[cfg(test)]
mod integration {
    use assert_cli;

    #[test]
    fn without_arg() {
        assert_cli::Assert::command(&["cargo", "run", "--features", "nolibsnark", "--", "compile", "-i", "./tests/add.code"])
            .fails()
            .and()
            .stderr().contains("Semantic analysis failed with: a is undefined")
            .unwrap();
    }
}