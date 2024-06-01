import Lake
open Lake DSL

package «Time» where
  -- add package configuration options here

lean_lib «Time» where
  -- add library configuration options here

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "ffi.o"
  let srcJob ← inputFile <| pkg.dir / "native" / "ffi.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

extern_lib libleanffi pkg := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
