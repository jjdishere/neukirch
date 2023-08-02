import Lake
open Lake DSL

package «neukirch» {
  -- add package configuration options here
}

lean_lib «AlgebraicNumberTheory» {
  -- add library configuration options here
}

@[default_target]
lean_exe «neukirch» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"