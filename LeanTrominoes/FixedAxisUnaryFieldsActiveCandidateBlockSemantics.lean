/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsCandidateBlockSemantics

/-! # Activation-sensitive candidate block semantics -/

namespace LeanTrominoes.FixedAxisUnaryFields

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

/-- Pointwise datum agreement for the simultaneously available activation,
axis, and candidate-template block streams.  Like their consumers, malformed
unequal outer lists stop at the first exhausted stream. -/
def ActiveDatumBlocks {Value : Type*} (datum : Option Value → Nat) :
    List Bool → List (List Bool) →
      List (List (Template Value)) → Prop
  | [], _, _ => True
  | _ :: _, [], [] => True
  | active :: actives, axes :: axisBlocks, templates :: templateBlocks =>
      List.Forall₂
        (fun axis template =>
          value active axis =
            datum (Template.activate active template).value)
        axes templates ∧
      ActiveDatumBlocks datum actives axisBlocks templateBlocks
  | _, _, _ => False

/-- Two aligned chunks concatenate when the three first chunks have the
same outer length. -/
theorem ActiveDatumBlocks.append
    {Value : Type*} {datum : Option Value → Nat}
    {firstActives secondActives : List Bool}
    {firstAxes secondAxes : List (List Bool)}
    {firstTemplates secondTemplates : List (List (Template Value))}
    (first : ActiveDatumBlocks datum
      firstActives firstAxes firstTemplates)
    (second : ActiveDatumBlocks datum
      secondActives secondAxes secondTemplates)
    (axesLength : firstActives.length = firstAxes.length)
    (templatesLength : firstActives.length = firstTemplates.length) :
    ActiveDatumBlocks datum
      (firstActives ++ secondActives)
      (firstAxes ++ secondAxes)
      (firstTemplates ++ secondTemplates) := by
  induction firstActives generalizing firstAxes firstTemplates with
  | nil =>
      have axesNil : firstAxes = [] :=
        List.eq_nil_of_length_eq_zero axesLength.symm
      have templatesNil : firstTemplates = [] :=
        List.eq_nil_of_length_eq_zero templatesLength.symm
      subst firstAxes
      subst firstTemplates
      exact second
  | cons active firstActives induction =>
      cases firstAxes with
      | nil => simp at axesLength
      | cons axes firstAxes =>
          cases firstTemplates with
          | nil => simp at templatesLength
          | cons templates firstTemplates =>
              simp only [List.length_cons, Nat.succ.injEq]
                at axesLength templatesLength
              exact ⟨first.1,
                induction first.2 axesLength templatesLength⟩

/-- Pointwise-aligned chunks compose through a common outer `flatMap`. -/
theorem ActiveDatumBlocks.flatMap
    {Index Value : Type*} (datum : Option Value → Nat)
    (indices : List Index) (actives : Index → List Bool)
    (axes : Index → List (List Bool))
    (templates : Index → List (List (Template Value)))
    (aligned : ∀ index ∈ indices,
      ActiveDatumBlocks datum
        (actives index) (axes index) (templates index))
    (axesLength : ∀ index ∈ indices,
      (actives index).length = (axes index).length)
    (templatesLength : ∀ index ∈ indices,
      (actives index).length = (templates index).length) :
    ActiveDatumBlocks datum
      (indices.flatMap actives)
      (indices.flatMap axes)
      (indices.flatMap templates) := by
  induction indices with
  | nil => trivial
  | cons index indices induction =>
      simp only [List.flatMap_cons]
      exact ActiveDatumBlocks.append
        (aligned index (by simp))
        (induction
          (fun item member => aligned item (by simp [member]))
          (fun item member => axesLength item (by simp [member]))
          (fun item member => templatesLength item (by simp [member])))
        (axesLength index (by simp))
        (templatesLength index (by simp))

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
    {Value : Type*} (datum : Option Value → Nat) (active : Bool)
    {axes : List Bool} {templates : List (Template Value)}
    (aligned : List.Forall₂
      (fun axis template =>
        value active axis =
          datum (Template.activate active template).value)
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
      exact List.Forall₂.cons head induction

/-- Activation-sensitive block agreement survives flattening into the
padded candidate stream. -/
theorem zip_blockActives_flatten_forall₂_candidates_of_active
    {Value : Type*} (datum : Option Value → Nat)
    (actives : List Bool) (axisBlocks : List (List Bool))
    (templateBlocks : List (List (Template Value)))
    (aligned : ActiveDatumBlocks datum
      actives axisBlocks templateBlocks) :
    List.Forall₂
      (fun tagged candidate =>
        value tagged.1 tagged.2 = datum candidate.value)
      (List.zip (blockActives actives axisBlocks) axisBlocks.flatten)
      (candidates actives templateBlocks) := by
  induction actives generalizing axisBlocks templateBlocks with
  | nil => simp [blockActives, candidates]
  | cons active actives induction =>
      cases axisBlocks with
      | nil =>
          cases templateBlocks with
          | nil => simp [blockActives, candidates]
          | cons templates templateBlocks =>
              simp [ActiveDatumBlocks] at aligned
      | cons axes axisBlocks =>
          cases templateBlocks with
          | nil => simp [ActiveDatumBlocks] at aligned
          | cons templates templateBlocks =>
              have head := aligned.1
              have tail := aligned.2
              simp only [blockActives, List.flatten_cons, candidates]
              rw [List.zip_append (by simp)]
              exact forall₂_append
                (zip_replicate_forall₂_map_activate
                  datum active head)
                (induction axisBlocks templateBlocks tail)

/-- Therefore an activation-sensitive block proof identifies the fixed-axis
stream with the datum mapped over all padded candidates. -/
theorem values_blockActives_eq_map_candidates_of_active
    {Value : Type*} (datum : Option Value → Nat)
    (actives : List Bool) (axisBlocks : List (List Bool))
    (templateBlocks : List (List (Template Value)))
    (aligned : ActiveDatumBlocks datum
      actives axisBlocks templateBlocks) :
    values axisBlocks.flatten (blockActives actives axisBlocks) =
      (candidates actives templateBlocks).map
        (datum ∘ Candidate.value) := by
  exact values_eq_map_candidateValue_of_forall₂ _ _ _ datum
    (zip_blockActives_flatten_forall₂_candidates_of_active
      datum actives axisBlocks templateBlocks aligned)

end LeanTrominoes.FixedAxisUnaryFields
