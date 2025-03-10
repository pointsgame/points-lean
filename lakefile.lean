import Lake

open Lake DSL

-- MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.17.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.17.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "0f9008e70927c4afac8ad2bc32f2f4fbda044096"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "e7fd1a415c80985ade02a021172834ca2139b0ca"

package «points»

@[default_target]
lean_lib «Points»

lean_exe «bench» where
  moreLinkArgs := #["-O3"]
  root := `Bench
