# [0.2.0] - 2025-09-29

- The TypeSet trait has been reworked for better ergonomics. The parser's TypeSet is now an associated type. Additional associated types and trait bounds have been added.
- The `MemoryRepr` trait has been removed.
- TypedValue's `String` is now also generic.
- TypedValue's `MaybeSignedInt` may now compare equal to `Int` and `SignedInt` if the inner number compares equal after casting.
- The string interner has been removed. The expression engine uses `Box<str>` as storage by default.
- `ExprContext::try_load_variable` and `address_of` now take `&mut self`.
- Added `declare` and `assign_variable` to `ExprContext`.
- `Context::parse` and variants to load a whole program for evaluation.
- Added `Context::evaluate_parsed` to evaluate pre-parsed expressions.
- Removed `Context::evaluate_expr_any` and `evaluate_any`. You can specify `evaluate` (and `evaluate_parsed`) to return `TypedValue`.
- Merged the `Load` and `Store` traits into `LoadStore`.
- Added `ExpressionVisitor::visit_right_hand_expression`.
- Added `TypedValue::modulo` for modulo operation.

# [0.1.0] - 2025-07-24

- Initial release

[0.2.0]: https://github.com/bugadani/somni/compare/somni-expr-v0.1.0...somni-expr-v0.2.0
[0.1.0]: https://github.com/bugadani/somni/releases/tag/somni-expr-v0.1.0
