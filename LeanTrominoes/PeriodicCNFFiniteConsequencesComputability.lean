/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFiniteConsequences
import Lean.Util.CollectAxioms

/-! # Computable search for the finite window forcing a Boolean consequence -/
namespace LeanTrominoes.PeriodicCNF.FiniteConsequences
variable {V : Type} [Primcodable V] [DecidableEq V]

omit [DecidableEq V] in
theorem falsifyingSeed_primrec : Primrec (@falsifyingSeed V) :=
  Primrec.list_map Primrec.id
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.not.comp (Primrec.snd.comp Primrec.snd)))

theorem finiteEntails_primrec :
    PrimrecPred (fun a : (PeriodicCNF V × Clause V) × Nat =>
      FiniteEntails a.1.1 a.1.2 a.2) := by
  have input : Primrec (fun a : (PeriodicCNF V × Clause V) × Nat =>
      ((a.1.1,falsifyingSeed a.1.2),a.2)) :=
    Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (falsifyingSeed_primrec.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  exact (FiniteSearch.check_primrec.comp
    (FiniteSearch.withSeed_primrec.comp input)).not

private theorem finiteEntails_decide_computable :
    Computable (fun a : (PeriodicCNF V × Clause V) × Nat =>
      decide (FiniteEntails a.1.1 a.1.2 a.2)) :=
  finiteEntails_primrec.decide.to_comp

attribute [local irreducible] FiniteEntails FiniteSearch.Check
  FiniteSearch.withSeed FiniteSearch.instantiate falsifyingSeed

noncomputable def searchRadius {Input : Type}
    (formula : Input → PeriodicCNF V) (clause : Input → Clause V)
    (forced : ∀ input, Entails (formula input) (clause input)) (input : Input) : Nat :=
  radius (formula input) (clause input) (forced input)

theorem searchRadius_computable {Input : Type} [Primcodable Input]
    {formula : Input → PeriodicCNF V} {clause : Input → Clause V}
    (formulaComputable : Computable formula) (clauseComputable : Computable clause)
    (forced : ∀ input, Entails (formula input) (clause input)) :
    Computable (searchRadius formula clause forced) := by
  have check : ComputablePred (fun a : Input × Nat =>
      FiniteEntails (formula a.1) (clause a.1) a.2) := by
    apply ComputablePred.computable_iff.mpr
    refine ⟨fun a => decide (FiniteEntails (formula a.1) (clause a.1) a.2),
      finiteEntails_decide_computable.comp
        (Computable.pair
          (Computable.pair (formulaComputable.comp Computable.fst)
            (clauseComputable.comp Computable.fst)) Computable.snd),?_⟩
    funext a
    apply propext
    simp
  have found := Computable.find check (fun input =>
    (entails_iff (formula input) (clause input)).1 (forced input))
  exact found.of_eq (fun _ => rfl)

omit [Primcodable V] in
theorem searchRadius_sound {Input : Type}
    (formula : Input → PeriodicCNF V) (clause : Input → Clause V)
    (forced : ∀ input, Entails (formula input) (clause input)) (input : Input)
    (a : V → Cell → Bool)
    (patch : ∀ c ∈ TrominoAssignment.boxCellList (searchRadius formula clause forced input),
      ∀ sourceClause ∈ (formula input).clauses, sourceClause.Holds a c) :
    Holds (clause input) a :=
  finiteEntails_sound (radius_spec _ _ (forced input)) a patch

open Lean Elab Command in
run_cmd do
  for name in [``searchRadius_computable,``searchRadius_sound] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicCNF.FiniteConsequences
