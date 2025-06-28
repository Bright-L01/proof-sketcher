/-
Lean 4 theorem extractor for Proof Sketcher.
Extracts theorem information and outputs JSON to stdout.

Usage: lean --run lean_extractor.lean -- --file path/to/file.lean --theorem theorem_name
-/

import Lean.Meta
import Lean.Elab
import Lean.Parser
import Lean.Environment
import Lean.Data.Json

open Lean Meta Elab Command

-- JSON output structure
structure TheoremInfo where
  name : String
  type : String
  dependencies : Array String
  docString : Option String
  success : Bool
deriving ToJson, FromJson

-- Helper to extract dependencies from expression
partial def extractDependencies (expr : Expr) : MetaM (Array Name) := do
  let mut deps : Array Name := #[]
  
  let rec visit (e : Expr) : MetaM (Array Name) := do
    match e with
    | .const name _ => 
      -- Filter out built-in constants and focus on meaningful dependencies
      if name.toString.startsWith "Nat." || 
         name.toString.startsWith "List." ||
         name.toString.startsWith "Eq." ||
         name.toString.startsWith "And." ||
         name.toString.startsWith "Or." ||
         (!name.toString.startsWith "_" && name.components.length > 1) then
        return #[name]
      else
        return #[]
    | .app f a => do
      let fdeps ← visit f
      let adeps ← visit a
      return fdeps ++ adeps
    | .lam _ _ body _ => visit body
    | .forallE _ _ body _ => visit body
    | .letE _ _ value body _ => do
      let vdeps ← visit value
      let bdeps ← visit body
      return vdeps ++ bdeps
    | .mdata _ expr => visit expr
    | _ => return #[]
  
  visit expr

-- Extract theorem information from environment
def extractTheoremInfo (env : Environment) (theoremName : String) : MetaM TheoremInfo := do
  let name := theoremName.toName
  
  match env.find? name with
  | none => 
    return { 
      name := theoremName, 
      type := "", 
      dependencies := #[], 
      docString := none, 
      success := false 
    }
  | some cinfo => do
    -- Get the type as a string
    let typeStr := toString cinfo.type
    
    -- Extract dependencies
    let deps ← extractDependencies cinfo.type
    let depStrings := deps.map (·.toString)
    
    -- Get docstring if available
    let docString := env.getModuleDocString? name
    
    return {
      name := theoremName,
      type := typeStr,
      dependencies := depStrings,
      docString := docString,
      success := true
    }

-- Parse command line arguments
def parseArgs (args : List String) : Option (String × String) := do
  let rec go (args : List String) (file : Option String) (theorem : Option String) : Option (String × String) :=
    match args with
    | [] => 
      match file, theorem with
      | some f, some t => some (f, t)
      | _, _ => none
    | "--file" :: f :: rest => go rest (some f) theorem
    | "--theorem" :: t :: rest => go rest file (some t)
    | _ :: rest => go rest file theorem
  
  go args none none

-- Main extraction function
def extractMain (filePath : String) (theoremName : String) : IO Unit := do
  -- Initialize Lean environment
  initSearchPath (← findSysroot)
  
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile filePath) filePath
  let (header, parserState, messages) := Parser.parseHeader inputCtx
  
  -- Check for parsing errors
  if messages.hasErrors then
    let errorInfo : TheoremInfo := {
      name := theoremName,
      type := "",
      dependencies := #[],
      docString := none,
      success := false
    }
    IO.println (toJson errorInfo).compress
    return
  
  let (env, messages) ← processHeader header {} messages inputCtx
  
  if messages.hasErrors then
    let errorInfo : TheoremInfo := {
      name := theoremName,
      type := "",
      dependencies := #[],
      docString := none,
      success := false
    }
    IO.println (toJson errorInfo).compress
    return
  
  -- Parse the rest of the file
  let commandState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState commandState
  
  -- Extract theorem information
  let result ← extractTheoremInfo s.env theoremName |>.run' {}
  
  -- Output JSON
  IO.println (toJson result).compress

-- Entry point
def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | none => 
    IO.eprintln "Usage: lean --run lean_extractor.lean -- --file <path> --theorem <name>"
    return 1
  | some (filePath, theoremName) => do
    try
      extractMain filePath theoremName
      return 0
    catch e =>
      let errorInfo : TheoremInfo := {
        name := theoremName,
        type := "",
        dependencies := #[],
        docString := none,
        success := false
      }
      IO.println (toJson errorInfo).compress
      IO.eprintln s!"Error: {e}"
      return 1

#eval main (← IO.getArgs)