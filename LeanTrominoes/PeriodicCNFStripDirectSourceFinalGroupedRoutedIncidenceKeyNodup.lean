/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyBlockSemantics

/-! # Uniqueness of grouped routed-incidence keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

private def routedIncidenceKeyBlock
    (start : Nat) (data : FinalFanOccurrenceData) : List Nat :=
  (directFinalOccurrenceRoutedIncidenceKeyOffsets data).map
    fun offset => start * 3 + offset

private def routedIncidenceKeysAux :
    Nat → List FinalFanOccurrenceData → List Nat
  | _, [] => []
  | start, data :: rest =>
      routedIncidenceKeyBlock start data ++
        routedIncidenceKeysAux
          (start + directFinalOccurrenceTripleBlockWidth data) rest

private theorem occurrenceBlocks_startsAux
    (start : Nat) (data : List FinalFanOccurrenceData) :
    (List.zipWith
      (fun blockStart datum => routedIncidenceKeyBlock blockStart datum)
      (PrefixSums.startsAux start
        (data.map directFinalOccurrenceTripleBlockWidth)) data).flatten =
      routedIncidenceKeysAux start data := by
  induction data generalizing start with
  | nil => rfl
  | cons datum data induction =>
      simp [routedIncidenceKeysAux, induction]

private theorem routedIncidenceKeyBlock_nodup
    (start : Nat) (data : FinalFanOccurrenceData) :
    (routedIncidenceKeyBlock start data).Nodup := by
  rcases data with ⟨atomControl, kind, polarity, direction⟩
  cases kind <;>
    simp [routedIncidenceKeyBlock,
      directFinalOccurrenceRoutedIncidenceKeyOffsets]

private theorem routedIncidenceKeyBlock_lt
    (start : Nat) (data : FinalFanOccurrenceData)
    (key : Nat) (keyMember : key ∈ routedIncidenceKeyBlock start data) :
    key < (start + directFinalOccurrenceTripleBlockWidth data) * 3 := by
  rcases data with ⟨atomControl, kind, polarity, direction⟩
  cases kind <;>
    simp [routedIncidenceKeyBlock,
      directFinalOccurrenceRoutedIncidenceKeyOffsets,
      directFinalOccurrenceTripleBlockWidth] at keyMember ⊢ <;>
    rcases keyMember with rfl | rfl | rfl <;> omega

private theorem routedIncidenceKeysAux_lower
    (start : Nat) (data : List FinalFanOccurrenceData)
    (key : Nat) (keyMember : key ∈ routedIncidenceKeysAux start data) :
    start * 3 ≤ key := by
  induction data generalizing start with
  | nil => simp [routedIncidenceKeysAux] at keyMember
  | cons datum data induction =>
      rw [routedIncidenceKeysAux, List.mem_append] at keyMember
      rcases keyMember with headMember | tailMember
      · unfold routedIncidenceKeyBlock at headMember
        rcases List.mem_map.mp headMember with ⟨offset, _offsetMember, rfl⟩
        omega
      · have tailLower := induction
          (start + directFinalOccurrenceTripleBlockWidth datum) tailMember
        omega

private theorem routedIncidenceKeysAux_nodup
    (start : Nat) (data : List FinalFanOccurrenceData) :
    (routedIncidenceKeysAux start data).Nodup := by
  induction data generalizing start with
  | nil => simp [routedIncidenceKeysAux]
  | cons datum data induction =>
      rw [routedIncidenceKeysAux, List.nodup_append]
      refine ⟨routedIncidenceKeyBlock_nodup start datum,
        induction (start + directFinalOccurrenceTripleBlockWidth datum), ?_⟩
      intro first firstMember second secondMember equal
      have firstLt := routedIncidenceKeyBlock_lt
        start datum first firstMember
      have secondLower := routedIncidenceKeysAux_lower
        (start + directFinalOccurrenceTripleBlockWidth datum)
        data second secondMember
      omega

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every routed suffix body has a distinct global variable-incidence key. -/
theorem directSourceFinalGroupedRoutedIncidenceKeys_nodup
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedRoutedIncidenceKeys
      decider symbols).Nodup := by
  rw [directSourceFinalGroupedRoutedIncidenceKeys_eq_occurrenceBlocks]
  change
    (List.zipWith
      (fun start data => routedIncidenceKeyBlock start data)
      (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
      (directSourceFinalGroupedOccurrenceData decider symbols)).flatten.Nodup
  unfold directSourceFinalGroupedOccurrenceTripleBlockStarts
    directSourceFinalGroupedOccurrenceTripleBlockWidths
  rw [show PrefixSums.starts _ = PrefixSums.startsAux 0 _ by rfl,
    occurrenceBlocks_startsAux]
  exact routedIncidenceKeysAux_nodup 0 _

end LeanTrominoes.PeriodicCNFStripReduction

end
