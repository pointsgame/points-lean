import Lake

open Lake DSL

-- MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.9.1"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.9.1"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "8a51034d049c6a229d88dd62f490778a377eec06"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "2cf1030dc2ae6b3632c84a09350b675ef3e347d0"

package «points»

@[default_target]
lean_lib «Points»

lean_exe «bench» where
  moreLinkArgs := #["-O3"]
  root := `Bench
