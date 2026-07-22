import Lake
open Lake DSL

package «test-lean» where

@[default_target]
lean_lib TestLean where
  globs := #[.one `«wasm2.0», .one `«custom_notation», .one `typing_lemmas]
