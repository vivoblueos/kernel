# [0.2.2] - 2025-10-23

- Fix parsing non-numeric literals that contain `_`.

# [0.2.1] - 2025-10-21

- Parse grouped numeric literals (`1_000_000`).

# [0.2.0] - 2025-09-29

- Hidden the tokenizer function
- Unified lexer/parser errors
- Parser no longer needs the whole source to be tokenized upfront
- Added TypeSet type parameter to the whole AST and the `parse` function
- `Expression::as_variable` has been removed
- Split `Expression` and `RightHandExpression`, added `LeftHandExpression`
- Support free-standing block scopes
- Added `location` getters to statement types
- Added `%` for modulo operation

# [0.1.0] - 2025-07-24

- Initial release

[0.2.0]: https://github.com/bugadani/somni/compare/somni-parser-v0.1.0...somni-parser-v0.2.0
[0.1.0]: https://github.com/bugadani/somni/releases/tag/somni-parser-v0.1.0
