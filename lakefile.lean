import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4"
require verso from git "https://github.com/leanprover/verso.git"@"main"
require subverso from git "https://github.com/leanprover/subverso.git"@"main"

package «leancourse» where
  -- add package configuration options here
  -- building the C code cost much more than the optimizations save
  moreLeancArgs := #["-O0"]
  -- work around clang emitting invalid linker optimization hints that lld rejects
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-ignore_optimization_hints"]
    else #[]

lean_lib «Leancourse» where
  -- add library configuration options here

@[default_target]
lean_exe «leancourse» where
  srcDir := "./"
  root := `Main


-- let MD4lean.MD_FLAG_TABLES true
