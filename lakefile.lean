import Lake

open Lake DSL

package quantum where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

require leanfmt from git
  "https://github.com/duckki/LeanFmt.git" @ "v0.2.0"

@[default_target]
lean_lib QuantumComputing where
