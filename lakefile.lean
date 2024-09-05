import Lake

open Lake DSL

-- MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.9.1"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.9.1"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec" @ "8a51034d049c6a229d88dd62f490778a377eec06"

package «points»

@[default_target]
lean_lib «Points»
