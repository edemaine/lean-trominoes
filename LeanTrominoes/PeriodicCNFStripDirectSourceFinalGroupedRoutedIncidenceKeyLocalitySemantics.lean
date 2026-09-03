/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyBlockSemantics
import LeanTrominoes.PrefixSumsGetElem

/-! # Occurrence-local membership of grouped routed-incidence keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace GroupedRoutedIncidenceKeyLocality

def keyBlock (start : Nat) (data : FinalFanOccurrenceData) : List Nat :=
  (directFinalOccurrenceRoutedIncidenceKeyOffsets data).map
    fun offset => start * 3 + offset

def keysFrom : Nat → List FinalFanOccurrenceData → List Nat
  | _, [] => []
  | start, data :: rest =>
      keyBlock start data ++
        keysFrom (start + directFinalOccurrenceTripleBlockWidth data) rest

def blockStartAt
    (start : Nat) (data : List FinalFanOccurrenceData) (index : Nat) : Nat :=
  start + ((data.take index).map
    directFinalOccurrenceTripleBlockWidth).sum

private theorem keyBlock_lt
    (start : Nat) (data : FinalFanOccurrenceData)
    (key : Nat) (keyMember : key ∈ keyBlock start data) :
    key < (start + directFinalOccurrenceTripleBlockWidth data) * 3 := by
  rcases data with ⟨atomControl, kind, polarity, direction⟩
  cases kind <;>
    simp [keyBlock, directFinalOccurrenceRoutedIncidenceKeyOffsets,
      directFinalOccurrenceTripleBlockWidth] at keyMember ⊢ <;>
    rcases keyMember with rfl | rfl | rfl <;> omega

private theorem keysFrom_lower
    (start : Nat) (data : List FinalFanOccurrenceData)
    (key : Nat) (keyMember : key ∈ keysFrom start data) :
    start * 3 ≤ key := by
  induction data generalizing start with
  | nil => simp [keysFrom] at keyMember
  | cons datum data induction =>
      rw [keysFrom, List.mem_append] at keyMember
      rcases keyMember with headMember | tailMember
      · unfold keyBlock at headMember
        rcases List.mem_map.mp headMember with
          ⟨offset, _offsetMember, rfl⟩
        omega
      · have tailLower := induction
          (start + directFinalOccurrenceTripleBlockWidth datum) tailMember
        omega

private theorem blockStartAt_zero
    (start : Nat) (data : FinalFanOccurrenceData)
    (rest : List FinalFanOccurrenceData) :
    blockStartAt start (data :: rest) 0 = start := by
  simp [blockStartAt]

private theorem blockStartAt_succ
    (start : Nat) (data : FinalFanOccurrenceData)
    (rest : List FinalFanOccurrenceData) (index : Nat) :
    blockStartAt start (data :: rest) (index + 1) =
      blockStartAt
        (start + directFinalOccurrenceTripleBlockWidth data) rest index := by
  simp [blockStartAt, List.take_succ_cons]
  omega

/-- Within the full interval occupied by one occurrence, membership in the
complete routed-key stream is exactly membership in that occurrence's local
three-key block. -/
theorem mem_keysFrom_iff_mem_keyBlock
    (start : Nat) (data : List FinalFanOccurrenceData)
    (index : Nat) (indexLt : index < data.length)
    (query : Nat)
    (lower : blockStartAt start data index * 3 ≤ query)
    (upper : query <
      (blockStartAt start data index +
        directFinalOccurrenceTripleBlockWidth
          (data.getD index default)) * 3) :
    query ∈ keysFrom start data ↔
      query ∈ keyBlock (blockStartAt start data index)
        (data.getD index default) := by
  induction data generalizing start index with
  | nil => simp at indexLt
  | cons datum data induction =>
      cases index with
      | zero =>
          rw [keysFrom, List.mem_append]
          simp only [blockStartAt_zero, List.getD_cons_zero] at lower upper ⊢
          constructor
          · intro member
            rcases member with headMember | tailMember
            · exact headMember
            · have tailLower := keysFrom_lower
                (start + directFinalOccurrenceTripleBlockWidth datum)
                data query tailMember
              omega
          · exact fun headMember => Or.inl headMember
      | succ index =>
          have tailIndexLt : index < data.length := by
            simpa using indexLt
          have startEq := blockStartAt_succ start datum data index
          have dataEq : (datum :: data).getD (index + 1) default =
              data.getD index default := by
            simp
          rw [keysFrom, List.mem_append, startEq, dataEq]
          have lower' :
              blockStartAt
                  (start + directFinalOccurrenceTripleBlockWidth datum)
                  data index * 3 ≤ query := by
            simpa [startEq] using lower
          have upper' : query <
              (blockStartAt
                  (start + directFinalOccurrenceTripleBlockWidth datum)
                  data index +
                directFinalOccurrenceTripleBlockWidth
                  (data.getD index default)) * 3 := by
            simpa [startEq, dataEq] using upper
          rw [induction
            (start + directFinalOccurrenceTripleBlockWidth datum)
            index tailIndexLt lower' upper']
          constructor
          · intro member
            rcases member with headMember | tailMember
            · have headLt := keyBlock_lt start datum query headMember
              have laterLower :
                  (start + directFinalOccurrenceTripleBlockWidth datum) * 3 ≤
                    blockStartAt
                        (start + directFinalOccurrenceTripleBlockWidth datum)
                        data index * 3 := by
                unfold blockStartAt
                omega
              omega
            · exact tailMember
          · exact fun tailMember => Or.inr tailMember

theorem occurrenceBlocks_eq_keysFrom
    (start : Nat) (data : List FinalFanOccurrenceData) :
    (List.zipWith
      (fun blockStart datum => keyBlock blockStart datum)
      (PrefixSums.startsAux start
        (data.map directFinalOccurrenceTripleBlockWidth)) data).flatten =
      keysFrom start data := by
  induction data generalizing start with
  | nil => rfl
  | cons datum data induction =>
      simp [keysFrom, induction]

end GroupedRoutedIncidenceKeyLocality

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

def directSourceFinalGroupedOccurrenceTripleBlockStartAt
    (symbols : List encoding.Γ) (index : Nat) : Nat :=
  (directSourceFinalGroupedOccurrenceTripleBlockStarts
    decider symbols).getD index 0

def directSourceFinalGroupedOccurrenceDataAt
    (symbols : List encoding.Γ) (index : Nat) : FinalFanOccurrenceData :=
  (directSourceFinalGroupedOccurrenceData decider symbols).getD index default

/-- A query inside one grouped occurrence's complete variable-incidence
interval is a routed key exactly when it is one of that occurrence's three
explicit scaled local offsets. -/
theorem directSourceFinalGroupedRoutedIncidenceKey_mem_iff_local
    (symbols : List encoding.Γ) (index query : Nat)
    (indexLt : index <
      (directSourceFinalGroupedOccurrenceData decider symbols).length)
    (lower :
      directSourceFinalGroupedOccurrenceTripleBlockStartAt
          decider symbols index * 3 ≤ query)
    (upper : query <
      (directSourceFinalGroupedOccurrenceTripleBlockStartAt
          decider symbols index +
        directFinalOccurrenceTripleBlockWidth
          (directSourceFinalGroupedOccurrenceDataAt
            decider symbols index)) * 3) :
    query ∈ directSourceFinalGroupedRoutedIncidenceKeys decider symbols ↔
      query ∈
        GroupedRoutedIncidenceKeyLocality.keyBlock
          (directSourceFinalGroupedOccurrenceTripleBlockStartAt
            decider symbols index)
          (directSourceFinalGroupedOccurrenceDataAt
            decider symbols index) := by
  let data := directSourceFinalGroupedOccurrenceData decider symbols
  change index < data.length at indexLt
  have startsIndexLt : index <
      (PrefixSums.starts
        (data.map directFinalOccurrenceTripleBlockWidth)).length := by
    rw [PrefixSums.starts_length, List.length_map]
    exact indexLt
  have widthsIndexLt : index <
      (data.map directFinalOccurrenceTripleBlockWidth).length := by
    simpa using indexLt
  have startEq :
      directSourceFinalGroupedOccurrenceTripleBlockStartAt
          decider symbols index =
        GroupedRoutedIncidenceKeyLocality.blockStartAt 0 data index := by
    unfold directSourceFinalGroupedOccurrenceTripleBlockStartAt
      directSourceFinalGroupedOccurrenceTripleBlockStarts
      directSourceFinalGroupedOccurrenceTripleBlockWidths
    rw [List.getD_eq_getElem _ _ startsIndexLt,
      PrefixSums.starts_getElem _ index widthsIndexLt]
    unfold GroupedRoutedIncidenceKeyLocality.blockStartAt
    rw [← List.map_take]
    simp
  have dataEq :
      directSourceFinalGroupedOccurrenceDataAt decider symbols index =
        data.getD index default := by
    rfl
  rw [directSourceFinalGroupedRoutedIncidenceKeys_eq_occurrenceBlocks]
  change query ∈
      (List.zipWith
        (fun blockStart datum =>
          GroupedRoutedIncidenceKeyLocality.keyBlock blockStart datum)
        (PrefixSums.starts
          (data.map directFinalOccurrenceTripleBlockWidth)) data).flatten ↔ _
  rw [show PrefixSums.starts _ = PrefixSums.startsAux 0 _ by rfl,
    GroupedRoutedIncidenceKeyLocality.occurrenceBlocks_eq_keysFrom]
  rw [startEq] at lower upper ⊢
  rw [dataEq] at upper ⊢
  exact GroupedRoutedIncidenceKeyLocality.mem_keysFrom_iff_mem_keyBlock
    0 data index indexLt query lower upper

end LeanTrominoes.PeriodicCNFStripReduction

end
