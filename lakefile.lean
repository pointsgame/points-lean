import Lake

open Lake DSL

-- MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.9.1"

package «points»

@[default_target]
lean_lib «Points»
