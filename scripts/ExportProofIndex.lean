/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/
import Lean
import ChannelRenyiContinuity

/-! Extract declaration metadata from the completed solution's elaborated
environment. Dependency edges are constants in stored types and proof/definition
bodies, not imports or textual mentions. This tool does not import the challenge. -/

open Lean Elab Command

namespace ProofIndex

def inProject (moduleName : Name) : Bool :=
  let s := moduleName.toString
  s.startsWith "QuantumChannelContinuity." ||
    s.startsWith "ChannelContinuity."

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

def constantNames (e : Expr) : Json :=
  toJson ((e.foldConsts #[] fun n ns => ns.push n.toString).qsort (· < ·))

elab "#export_proof_index " output:str : command => do
  let env ← getEnv
  let mut entries : Array Json := #[]
  let names := env.constants.toList.map Prod.fst |>.toArray.qsort
    (fun a b => a.toString < b.toString)
  for name in names do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[moduleIdx.toNat]!
    if !inProject moduleName then continue
    let info := env.find? name |>.get!
    let range ← findDeclarationRanges? name
    let doc ← liftIO <| findDocString? env name
    let typeText ← liftTermElabM <| do
      return (← Meta.ppExpr info.type).pretty
    let value := info.value? (allowOpaque := true)
    let privateName := privateToUserName? name
    let line := range.map (·.selectionRange.pos.line)
    entries := entries.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("displayName", toJson (privateName.getD name).toString),
      ("kind", toJson (kind info)),
      ("module", toJson moduleName.toString),
      ("file", toJson (moduleName.toString.replace "." "/" ++ ".lean")),
      ("line", toJson line),
      ("private", toJson privateName.isSome),
      ("internal", toJson name.isInternalDetail),
      ("type", toJson typeText),
      ("docstring", toJson doc),
      ("hasBody", toJson value.isSome),
      ("typeDeps", constantNames info.type),
      ("proofDeps", value.map constantNames |>.getD (toJson (#[] : Array String))) ]
  let result := Json.mkObj [
    ("rootModule", toJson "ChannelRenyiContinuity"),
    ("declarations", toJson entries) ]
  liftIO <| IO.FS.writeFile output.getString (result.pretty ++ "\n")
  logInfo m!"Exported {entries.size} project declarations to {output.getString}"

end ProofIndex

#export_proof_index ".lake/proof-index/raw.json"
