import Lake
open Lake DSL

package JohnDoe

@[defaultTarget]
lean_lib JohnDoe

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

require UsCourts from git
  "https://github.com/ammkrn/UsCourts.git"@"master"

--require UsCourts from ".."/"UsCourts"
--require mathlib from ".."/"Mathlib4"