import Lake
open Lake DSL

package «MATH» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`,
    ⟨`linter.deprecated, true⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MATH» where
  -- add any library configuration options here

lean_lib «CLAUDE» where
  globs := #[.submodules `CLAUDE]
