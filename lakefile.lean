import Lake
open Lake DSL

abbrev linter : Array LeanOption := #[
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.missingEnd, true⟩,
  ⟨`linter.cdot, true⟩,
  ⟨`linter.dollarSyntax, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.longLine, true⟩,
  ⟨`linter.oldObtain, true⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.setOption, true⟩
]

abbrev options := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ] ++ linter.map fun s ↦ { s with name := `weak ++ s.name }

package «LTFP» where
  leanOptions := options
  moreServerOptions := linter

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib «LTFP» where
  globs := #[.andSubmodules `LTFP]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
