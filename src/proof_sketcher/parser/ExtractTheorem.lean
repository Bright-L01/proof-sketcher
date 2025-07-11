/-!
# Theorem Extractor for Proof Sketcher

This module extracts theorem information from Lean 4 files.
It outputs JSON with theorem type, tactics, dependencies, and docstrings.
-/

import Lean
import Lean.Meta
import Lean.Elab.Command
import Lean.Parser

open Lean Meta Elab Command

/-- Information about a theorem to be serialized as JSON -/
structure TheoremData where
  name : String
  type : String
  value : String
  docString : Option String
  tactics : Array String
  dependencies : Array String
  isAxiom : Bool
  deriving Lean.ToJson, Lean.FromJson

/-- Extract tactic invocations from a syntax tree -/
partial def extractTacticsFromSyntax (stx : Syntax) : Array String :=
  match stx with
  | Syntax.node _ kind args =>
    let kindStr := kind.toString
    let tactics :=
      if kindStr.endsWith ".tactic" || kindStr.contains "Tactic" then
        -- Extract the actual tactic name (last component)
        let tacticName := kindStr.split (· == '.') |>.getLast!
        #[tacticName]
      else if kindStr == "`tactic" then
        -- Handle quoted tactics
        if args.size > 0 then
          #[args[0]!.prettyPrint.pretty]
        else #[]
      else #[]
    tactics ++ args.concatMap extractTacticsFromSyntax
  | Syntax.atom _ val =>
    -- Direct tactic names like "simp", "rfl", etc.
    if val.all Char.isAlpha then #[val] else #[]
  | _ => #[]

/-- Extract dependencies from an expression -/
partial def extractDeps (e : Expr) (visited : NameSet := {}) : MetaM NameSet := do
  if visited.contains e.hash then
    return visited
  let visited := visited.insert e.hash

  match e with
  | .const name _ =>
    let nameStr := name.toString
    -- Include mathlib and meaningful dependencies, exclude internals
    if !nameStr.startsWith "_" &&
       !nameStr.startsWith "Lean." &&
       !nameStr.startsWith "Classical" &&
       !nameStr.startsWith "sorryAx" &&
       nameStr != "True" && nameStr != "False" &&
       nameStr.contains "." then
      return visited.insert name
    else
      return visited
  | .app f a => do
    let visited ← extractDeps f visited
    extractDeps a visited
  | .lam _ type body _ => do
    let visited ← extractDeps type visited
    extractDeps body visited
  | .forallE _ type body _ => do
    let visited ← extractDeps type visited
    extractDeps body visited
  | .letE _ type value body _ => do
    let visited ← extractDeps type visited
    let visited ← extractDeps value visited
    extractDeps body visited
  | .mdata _ expr => extractDeps expr visited
  | _ => return visited

/-- Extract tactics from a proof expression by pattern matching common tactic combinators -/
partial def extractTacticsFromProof (e : Expr) : Array String :=
  match e with
  | .const name _ =>
    let nameStr := name.toString
    -- Common tactics that appear as constants
    if nameStr.endsWith ".simp" || nameStr.endsWith ".rfl" ||
       nameStr.endsWith ".trivial" || nameStr.endsWith ".assumption" ||
       nameStr.endsWith ".exact" || nameStr.endsWith ".apply" then
      #[nameStr.split (· == '.') |>.getLast!]
    else #[]
  | .app f a =>
    -- Recursively extract from function and argument
    extractTacticsFromProof f ++ extractTacticsFromProof a
  | .lam _ _ body _ =>
    extractTacticsFromProof body
  | .letE _ _ value body _ =>
    extractTacticsFromProof value ++ extractTacticsFromProof body
  | _ => #[]

/-- Process a single theorem -/
def processTheorem (env : Environment) (name : Name) : MetaM TheoremData := do
  let some info := env.find? name | throw $ IO.userError s!"Theorem {name} not found"

  -- Format type
  let type ← ppExpr info.type
  let typeStr := toString type

  -- Check if it's an axiom
  let (valueStr, isAxiom, tactics) ← match info.value? with
  | none => return ("axiom", true, #[])
  | some val => do
    let pp ← ppExpr val
    -- Extract tactics from the proof term by analyzing its structure
    let tactics := extractTacticsFromProof val
    return (toString pp, false, tactics)

  -- Get docstring
  let docString ← findDocString? env name

  -- Extract dependencies
  let typeDeps ← extractDeps info.type {}
  let valueDeps ← match info.value? with
  | none => pure {}
  | some val => extractDeps val {}

  let allDeps := (typeDeps.toArray ++ valueDeps.toArray).map toString
  let uniqueDeps := allDeps.toList.eraseDups.toArray

  return {
    name := name.toString
    type := typeStr
    value := valueStr
    docString := docString.map (·.toFormat.pretty)
    tactics := tactics
    dependencies := uniqueDeps
    isAxiom := isAxiom
  }

/-- Main entry point for the extractor -/
def main (args : List String) : IO UInt32 := do
  try
    -- Parse arguments
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

    -- Initialize Lean
    initSearchPath (← findSysroot)

    -- Parse the file
    let input ← IO.FS.readFile file
    let inputCtx := Parser.mkInputContext input file
    let (header, parserState, messages) := Parser.parseHeader inputCtx

    if messages.hasErrors then
      throw $ IO.userError "Parse errors in header"

    let (env, messages) ← processHeader header {} messages inputCtx

    if messages.hasErrors then
      throw $ IO.userError "Errors processing header"

    -- Process commands
    let commandState := Command.mkState env messages {}
    let s ← IO.processCommands inputCtx parserState commandState

    -- Extract theorem data
    let name := theorem.toName
    let data ← processTheorem s.env name |>.run' {}

    -- Output JSON
    IO.println (toJson data).compress
    return 0

  catch e =>
    -- Output error as JSON
    let errorData : TheoremData := {
      name := args.getD 3 "unknown"
      type := ""
      value := ""
      docString := some s!"Error: {e}"
      tactics := #[]
      dependencies := #[]
      isAxiom := false
    }
    IO.println (toJson errorData).compress
    return 1
