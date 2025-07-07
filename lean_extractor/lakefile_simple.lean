import Lake
open Lake DSL

package «extract_theorem» where
  -- add package configuration options here

lean_lib «ExtractTheorem» where
  -- add library configuration options here

@[default_target]
lean_exe «extract» where
  root := `ExtractTheorem