import Lake
open Lake DSL
open System (FilePath)

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.17.0-rc1"
require verso from git "https://github.com/leanprover/verso.git"@"v4.17.0-rc1"

require «verso-manual» from git "https://github.com/leanprover/reference-manual.git"@"e3b344835c794d7c0f6921bcff0c57c516d4a895"

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

/-- Ensure that the subverso-extract-mod executable is available -/
target subversoExtractMod : FilePath := do
  if let some pkg := ← findPackage? `subverso then
    if let some exe := pkg.findLeanExe? `«subverso-extract-mod» then
      exe.recBuildExe
    else
      failure
  else
    failure

@[default_target]
lean_exe «leancourse» where
  srcDir := "./"
  extraDepTargets := #[`subversoExtractMod]
  root := `Main


-- let MD4lean.MD_FLAG_TABLES true
