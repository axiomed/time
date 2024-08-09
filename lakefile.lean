import Lake
open Lake DSL

package Time where
  precompileModules := true

lean_lib Time where

lean_exe time where
  root := `Main

target native.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "native.o"
  let srcJob ← inputFile <| pkg.dir / "native" / "native.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "clang++" getLeanTrace

extern_lib libleanffi pkg := do
  let ffiO ← native.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
