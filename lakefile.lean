import Lake
open Lake DSL

package «MasterDiss» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «hyperplane» {
  -- add any library configuration options here
}

lean_lib «Polytope» {
  -- add any library configuration options here
}

lean_lib «polar» {
  -- add any library configuration options here
}

lean_lib «pre» {
  -- add any library configuration options here
}

@[default_target]
lean_exe «Main» {
  root := `Main
}