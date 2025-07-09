import Lean
import Lean.Meta
import Lean.Elab.Command
import Lean.Parser

/-!
# Simple Theorem Extractor for Proof Sketcher

This is a minimal version that works without Mathlib dependencies.
-/

open Lean Meta Elab Command

/-- Information about a theorem to be serialized as JSON -/
structure TheoremData where
  name : String
  type : String
  statement : String
  value : String
  docString : Option String
  tactics : Array String
  dependencies : Array String
  isAxiom : Bool
  deriving Lean.ToJson, Lean.FromJson

/-- Extract dependencies from an expression -/
partial def extractDependencies (e : Expr) : MetaM (Array Name) := do
  let mut deps : Array Name := #[]

  let rec collect (expr : Expr) : MetaM Unit := do
    match expr with
    | .const name _ =>
      let nameStr := name.toString
      if !nameStr.startsWith "_" &&
         !nameStr.startsWith "Lean." &&
         nameStr != "True" && nameStr != "False" &&
         nameStr.contains '.' then
        deps := deps.push name
    | .app f a => do
      collect f
      collect a
    | .lam _ type body _ => do
      collect type
      collect body
    | .forallE _ type body _ => do
      collect type
      collect body
    | _ => return ()

  collect e
  return deps

/-- Process a theorem -/
def processTheorem (env : Environment) (name : Name) : MetaM TheoremData := do
  let some info := env.find? name | throw $ IO.userError s!"Theorem {name} not found"

  let type ← ppExpr info.type
  let typeStr := toString type

  let (valueStr, isAxiom) ← match info.value? with
  | none => return ("axiom", true)
  | some val => do
    let pp ← ppExpr val
    return (toString pp, false)

  let docString ← findDocString? env name
  let deps ← extractDependencies info.type
  let uniqueDeps := deps.map toString

  return {
    name := name.toString
    type := typeStr
    statement := typeStr
    value := valueStr
    docString := docString.map (·.toFormat.pretty)
    tactics := #["rfl"] -- Simplified for now
    dependencies := uniqueDeps
    isAxiom := isAxiom
  }

def main (args : List String) : IO UInt32 := do
  try
    let mut fileName : Option String := none
    let mut theoremName : Option String := none
    let mut i := 0

    while i < args.length do
      match args[i]? with
      | some "--file" =>
        fileName := args[i+1]?
        i := i + 2
      | some "--theorem" =>
        theoremName := args[i+1]?
        i := i + 2
      | _ => i := i + 1

    let some file := fileName | throw $ IO.userError "Missing --file argument"
    let some theorem := theoremName | throw $ IO.userError "Missing --theorem argument"

    initSearchPath (← findSysroot)

    let input ← IO.FS.readFile file
    let inputCtx := Parser.mkInputContext input file
    let (header, parserState, messages) := Parser.parseHeader inputCtx

    if messages.hasErrors then
      throw $ IO.userError "Parse errors"

    let (env, messages) ← processHeader header {} messages inputCtx

    if messages.hasErrors then
      throw $ IO.userError "Header errors"

    let commandState := Command.mkState env messages {}
    let finalState ← IO.processCommands inputCtx parserState commandState

    let name := theorem.toName
    let data ← processTheorem finalState.env name |>.run' {}

    IO.println (toJson data).compress
    return 0

  catch e =>
    IO.eprintln s!"Error: {e}"
    return 1
