/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFields
import LeanTrominoes.PaddedSupportedCandidateBlocks

/-! # Candidate semantics of fixed-axis unary values -/

namespace LeanTrominoes.FixedAxisUnaryFields

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

private theorem zipWith_value_eq_map_zip (actives axes : List Bool) :
    List.zipWith value actives axes =
      (List.zip actives axes).map fun tagged =>
        value tagged.1 tagged.2 := by
  induction actives generalizing axes with
  | nil => rfl
  | cons active actives induction =>
      cases axes with
      | nil => rfl
      | cons axis axes =>
          simp only [List.zipWith_cons_cons, List.zip_cons_cons,
            List.map_cons]
          rw [induction axes]

private theorem map_eq_map_of_forall₂
    {First Second Result : Type*}
    (first : First → Result) (second : Second → Result)
    {firsts : List First} {seconds : List Second}
    (aligned : List.Forall₂
      (fun firstValue secondValue =>
        first firstValue = second secondValue)
      firsts seconds) :
    firsts.map first = seconds.map second := by
  induction aligned with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons]
      rw [head, induction]

/-- Pointwise alignment of activation/axis pairs with padded candidates
identifies the complete fixed-axis value stream with mapped candidate data. -/
theorem values_eq_map_candidateValue_of_forall₂
    {Value : Type*} (axes actives : List Bool)
    (candidates : List (Candidate Value))
    (datum : Option Value → Nat)
    (aligned : List.Forall₂
      (fun tagged candidate =>
        value tagged.1 tagged.2 = datum candidate.value)
      (List.zip actives axes) candidates) :
    values axes actives = candidates.map (datum ∘ Candidate.value) := by
  unfold values
  rw [zipWith_value_eq_map_zip]
  exact map_eq_map_of_forall₂
    (fun tagged : Bool × Bool => value tagged.1 tagged.2)
    (datum ∘ Candidate.value) aligned

/-- Activating one template preserves the aligned datum relation. -/
theorem value_eq_datum_activate
    {Value : Type*} (datum : Option Value → Nat)
    (datumNone : datum none = 0) (active axis : Bool)
    (template : Template Value)
    (activeValue : value true axis = datum (some template.value)) :
    value active axis = datum (Template.activate active template).value := by
  cases active <;>
    simp [value, Template.activate, datumNone] at activeValue ⊢
  exact activeValue

end LeanTrominoes.FixedAxisUnaryFields
