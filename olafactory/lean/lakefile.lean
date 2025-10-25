import Lake
open Lake DSL

package «dtqc» where
  -- DTQC Formal Verification for Olfaction

lean_lib «DTQC» where
  -- Core DTQC theorems and definitions

@[default_target]
lean_exe «dtqc» where
  root := `Main
