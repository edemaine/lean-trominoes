/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsCandidateSemantics

/-! # Block candidate semantics of fixed-axis unary values -/

namespace LeanTrominoes.FixedAxisUnaryFields

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

/-- Repeat each predicate activation once per entry of its axis block. -/
def blockActives : List Bool → List (List Bool) → List Bool
  | active :: actives, axes :: axisBlocks =>
      List.replicate axes.length active ++
        blockActives actives axisBlocks
  | _, _ => []

private theorem forall₂_append
    {First Second : Type*} {Relation : First → Second → Prop}
    {firstHead firstTail : List First}
    {secondHead secondTail : List Second}
    (head : List.Forall₂ Relation firstHead secondHead)
    (tail : List.Forall₂ Relation firstTail secondTail) :
    List.Forall₂ Relation
      (firstHead ++ firstTail) (secondHead ++ secondTail) := by
  induction head with
  | nil => exact tail
  | cons relation rest induction =>
      exact List.Forall₂.cons relation induction

private theorem zip_replicate_forall₂_map_activate
    {Value : Type*} (datum : Option Value → Nat)
    (datumNone : datum none = 0) (active : Bool)
    {axes : List Bool} {templates : List (Template Value)}
    (aligned : List.Forall₂
      (fun axis template =>
        value true axis = datum (some template.value))
      axes templates) :
    List.Forall₂
      (fun tagged candidate =>
        value tagged.1 tagged.2 = datum candidate.value)
      (List.zip (List.replicate axes.length active) axes)
      (templates.map (Template.activate active)) := by
  induction aligned with
  | nil => exact List.Forall₂.nil
  | cons head tail induction =>
      simp only [List.length_cons, List.replicate_succ,
        List.zip_cons_cons, List.map_cons]
      exact List.Forall₂.cons
        (value_eq_datum_activate datum datumNone active _ _ head)
        induction

/-- Blockwise axis/template alignment survives runtime activation and
flattening into the padded candidate stream. -/
theorem zip_blockActives_flatten_forall₂_candidates
    {Value : Type*} (datum : Option Value → Nat)
    (datumNone : datum none = 0) (actives : List Bool)
    {axisBlocks : List (List Bool)}
    {templateBlocks : List (List (Template Value))}
    (aligned : List.Forall₂
      (List.Forall₂ fun axis template =>
        value true axis = datum (some template.value))
      axisBlocks templateBlocks) :
    List.Forall₂
      (fun tagged candidate =>
        value tagged.1 tagged.2 = datum candidate.value)
      (List.zip (blockActives actives axisBlocks) axisBlocks.flatten)
      (candidates actives templateBlocks) := by
  induction aligned generalizing actives with
  | nil => simp [blockActives, candidates]
  | cons head tail induction =>
      cases actives with
      | nil => simp [blockActives, candidates]
      | cons active actives =>
          simp only [blockActives, List.flatten_cons, candidates]
          rw [List.zip_append (by simp)]
          exact forall₂_append
            (zip_replicate_forall₂_map_activate
              datum datumNone active head)
            (induction actives)

/-- Hence aligned fixed axis/template blocks compute exactly a datum mapped
over the padded candidate values. -/
theorem values_blockActives_eq_map_candidates
    {Value : Type*} (datum : Option Value → Nat)
    (datumNone : datum none = 0) (actives : List Bool)
    {axisBlocks : List (List Bool)}
    {templateBlocks : List (List (Template Value))}
    (aligned : List.Forall₂
      (List.Forall₂ fun axis template =>
        value true axis = datum (some template.value))
      axisBlocks templateBlocks) :
    values axisBlocks.flatten (blockActives actives axisBlocks) =
      (candidates actives templateBlocks).map
        (datum ∘ Candidate.value) := by
  exact values_eq_map_candidateValue_of_forall₂ _ _ _ datum
    (zip_blockActives_flatten_forall₂_candidates
      datum datumNone actives aligned)

end LeanTrominoes.FixedAxisUnaryFields
