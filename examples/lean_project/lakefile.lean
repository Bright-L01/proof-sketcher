import Lake
open Lake DSL

package «proof-sketcher-examples» where
  -- add package configuration options here

lean_lib «ProofSketcherExamples» where
  -- add library configuration options here

@[default_target]
lean_exe «proof-sketcher-examples» where
  root := `Main