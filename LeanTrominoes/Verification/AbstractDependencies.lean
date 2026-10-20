/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GraphAbstract
import LeanTrominoes.TilingAbstract
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Meta.Transform


/-! # Verifying the public abstracts' dependency boundary

Check every public declaration's type and every public definition's body,
following references transitively within the project. Only the three abstract
modules may contribute project definitions; Mathlib and lean-wang are accepted
background libraries. Proof bodies, including structure law fields, may use the full implementation. Every
public declaration is also checked for unexpected axioms.
-/

private def nonProofConstants (expression : Lean.Expr) : Lean.MetaM (Array Lean.Name) := do
  let visit : StateT (Array Lean.Name) Lean.MetaM Lean.Expr :=
    Lean.Meta.transform expression (pre := fun term => do
      if ← Lean.Meta.isProof term then return .done term
      match term with
      | .const name _ | .proj name _ _ => modify fun names => names.push name
      | _ => pure ()
      return .continue)
  return (← visit.run #[]).2

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`LeanTrominoes.GraphAbstract,
    `LeanTrominoes.TilingAbstract,`LeanTrominoes.ComplexityAbstract]
  let mut roots : Array Name := #[]
  for (name,_) in env.constants.toList do
    if name.toString.startsWith "LeanTrominoes.GraphAbstract." ||
       name.toString.startsWith "LeanTrominoes.TilingAbstract." ||
       name.toString.startsWith "LeanTrominoes.ComplexityAbstract." then
      if let some index := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[index.toNat]! then
          roots := roots.push name
  let mut pending : Array Name := #[]
  for root in roots do
    let some info := env.find? root | throwError "Missing public endpoint {root}"
    pending := pending ++ info.type.getUsedConstants
    if let .defnInfo defn := info then
      pending := pending ++ (← liftTermElabM (nonProofConstants defn.value))
    let axioms ← Lean.collectAxioms root
    let extra := axioms.filter fun ax => ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "Unexpected axioms in {root}: {extra}"
  let mut seen : NameSet := {}
  let mut count : Nat := 0
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if let some index := env.getModuleIdxFor? name then
        let module := env.header.moduleNames[index.toNat]!
        if module.toString.startsWith "LeanTrominoes." then
          unless modules.contains module do
            throwError "Implementation reference in public signature/definition: {name} from {module}"
          let some info := env.find? name | throwError "Missing declaration {name}"
          pending := pending ++ info.type.getUsedConstants
          if let .defnInfo defn := info then
            pending := pending ++ (← liftTermElabM (nonProofConstants defn.value))
          count := count+1
  logInfo m!"All {roots.size} public declarations: standard axioms only. Transitive definition/signature audit passed ({count} declarations in the abstract suite)."
