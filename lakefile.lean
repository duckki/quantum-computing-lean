import Lake
open Lake DSL

package quantum where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib Quantum where
