/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationIncidenceIndices
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationPackedWindow

/-! # Vertex constraints as bounded incidence-index tests -/
namespace LeanTrominoes.TrichromaticGraphOrientation.LineWindow
open PeriodicOneInThree

def indexValue (input : Input) (word index : Nat) : Bool :=
  let literal := (incidenceAt input index).2.1
  assignment input (decodeWord input word) literal.atom literal.offset == literal.value

def Selected (input : Input) (vertex word index : Nat) : Prop :=
  (incidenceAt input index).1 = vertex ∧ indexValue input word index = true

instance (input : Input) (vertex word index : Nat) : Decidable (Selected input vertex word index) := by
  unfold Selected; infer_instance

def selectedIndices (input : Input) (vertex word : Nat) : Finset Nat :=
  ((List.range (2*input.2.length)).filter fun index => decide (Selected input vertex word index)).toFinset

theorem mem_selectedIndices (input : Input) (vertex word index : Nat) :
    index ∈ selectedIndices input vertex word ↔ index < 2*input.2.length ∧ Selected input vertex word index := by
  simp [selectedIndices]

theorem selected_card (input : Input) (vertex word : Nat) :
    (clauseValues (assignment input (decodeWord input word)) (0,0) (incoming input vertex)).count true =
      (selectedIndices input vertex word).card := by
  rw [selectedIndices,List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  unfold clauseValues incoming endsAt
  rw [ends_eq_incidenceIndices]
  have helper (indices : List Nat) :
      ((indices.filter fun index => (incidenceAt input index).1 = vertex).map
        (indexValue input word)).count true =
        (indices.filter fun index => decide (Selected input vertex word index)).length := by
    induction indices with
    | nil => rfl
    | cons index indices ih =>
      by_cases owner : (incidenceAt input index).1 = vertex <;>
        cases inward : indexValue input word index <;>
        simpa [Selected,owner,inward] using ih
  have result := helper (List.range (2*input.2.length))
  unfold indexValue at result
  simpa [List.filter_map,List.map_map,Function.comp_def,Cell.add] using result

theorem exactlyOne_iff_unique (input : Input) (vertex word : Nat) :
    ClauseHolds (assignment input (decodeWord input word)) (0,0) (incoming input vertex) ↔
      ∃ index < 2*input.2.length, Selected input vertex word index ∧
        ∀ other < 2*input.2.length, Selected input vertex word other → other = index := by
  rw [ClauseHolds,ExactlyOne,selected_card,Finset.card_eq_one]
  constructor
  · rintro ⟨index,equal⟩
    have member : index ∈ selectedIndices input vertex word := by rw [equal]; simp
    obtain ⟨bound,selected⟩ := (mem_selectedIndices input vertex word index).mp member
    refine ⟨index,bound,selected,?_⟩
    intro other otherBound otherSelected
    have member := (mem_selectedIndices input vertex word other).mpr ⟨otherBound,otherSelected⟩
    simpa only [equal,Finset.mem_singleton] using member
  · rintro ⟨index,bound,selected,unique⟩
    refine ⟨index,?_⟩
    ext other
    rw [mem_selectedIndices,Finset.mem_singleton]
    constructor
    · rintro ⟨otherBound,otherSelected⟩; exact unique other otherBound otherSelected
    · rintro rfl; exact ⟨bound,selected⟩

theorem coherent_iff_indices (input : Input) (vertex word : Nat) :
    Coherent (assignment input (decodeWord input word)) (0,0) (incoming input vertex) ↔
      ∀ first < 2*input.2.length, (incidenceAt input first).1 = vertex →
        ∀ second < 2*input.2.length, (incidenceAt input second).1 = vertex →
          indexValue input word first = indexValue input word second := by
  have incomingMember (literal : PeriodicLiteral Nat) : literal ∈ incoming input vertex ↔
      ∃ index < 2*input.2.length, (incidenceAt input index).1 = vertex ∧
        (incidenceAt input index).2.1 = literal := by
    simp only [incoming,endsAt,ends_eq_incidenceIndices,List.mem_map,List.mem_filter,List.mem_range]
    constructor
    · rintro ⟨incidence,⟨⟨index,bound,rfl⟩,owner⟩,rfl⟩
      exact ⟨index,bound,by simpa using owner,rfl⟩
    · rintro ⟨index,bound,owner,rfl⟩
      exact ⟨_,⟨⟨index,bound,rfl⟩,by simpa using owner⟩,rfl⟩
  have holds (index : Nat) : (incidenceAt input index).2.1.Holds
      (assignment input (decodeWord input word)) (0,0) ↔ indexValue input word index = true := by
    simp [PeriodicLiteral.Holds,indexValue,Cell.add]
  have boolEq (first second : Bool) : (first = true ↔ second = true) ↔ first = second := by
    cases first <;> cases second <;> decide
  constructor
  · intro h first firstBound firstOwner second secondBound secondOwner
    apply (boolEq _ _).mp
    rw [← holds first,← holds second]
    exact h _ ((incomingMember _).mpr ⟨first,firstBound,firstOwner,rfl⟩)
      _ ((incomingMember _).mpr ⟨second,secondBound,secondOwner,rfl⟩)
  · intro h literal literalMember other otherMember
    obtain ⟨first,firstBound,firstOwner,rfl⟩ := (incomingMember literal).mp literalMember
    obtain ⟨second,secondBound,secondOwner,rfl⟩ := (incomingMember other).mp otherMember
    rw [holds first,holds second]
    exact (boolEq _ _).mpr (h first firstBound firstOwner second secondBound secondOwner)

end LeanTrominoes.TrichromaticGraphOrientation.LineWindow
