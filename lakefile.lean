import Lake
open Lake DSL

package «MasterDiss» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «src» {
}

@[default_target]
lean_exe «Main» {
  root := `Main
}
