/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanKindSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixSemantics

/-! # Occurrence-block indexing of grouped variable incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- The finite query block selected by a grouped fan/slot has three times
the triple width stored in its aligned occurrence record. -/
theorem groupedVariableIncidencePrefixQueryBlock_length_eq_occurrenceWidth
    (pair : GroupedVariableFanSlot) (data : FinalFanOccurrenceData)
    (kindEq :
      pair.1.kind (groupedVariableFanSiteSlot pair.2) = data.kind) :
    (groupedVariableIncidencePrefixQueryBlock pair).length =
      3 * directFinalOccurrenceTripleBlockWidth data := by
  rw [groupedVariableIncidencePrefixQueryBlock_length,
    groupedVariableIncidenceTriples_length]
  unfold directFinalOccurrenceTripleBlockWidth
  rw [← kindEq]
  cases pair.1.kind (groupedVariableFanSiteSlot pair.2) <;> rfl

private theorem zipIdx_occurrenceBlocks
    (start : Nat) (pairs : List GroupedVariableFanSlot)
    (data : List FinalFanOccurrenceData)
    (aligned : List.Forall₂
      (fun pair datum =>
        pair.1.kind (groupedVariableFanSiteSlot pair.2) = datum.kind)
      pairs data) :
    (pairs.flatMap groupedVariableIncidencePrefixQueryBlock).zipIdx
        (3 * start) =
      (List.zipWith
        (fun blockStart pair =>
          (groupedVariableIncidencePrefixQueryBlock pair).zipIdx
            (3 * blockStart))
        (PrefixSums.startsAux start
          (data.map directFinalOccurrenceTripleBlockWidth))
        pairs).flatten := by
  induction aligned generalizing start with
  | nil => rfl
  | @cons pair datum pairs data kindEq aligned induction =>
      rw [List.flatMap_cons, List.zipIdx_append,
        groupedVariableIncidencePrefixQueryBlock_length_eq_occurrenceWidth
          pair datum kindEq]
      simp only [List.map_cons, PrefixSums.startsAux_cons,
        List.zipWith_cons_cons, List.flatten_cons]
      rw [show 3 * start + 3 * directFinalOccurrenceTripleBlockWidth datum =
          3 * (start + directFinalOccurrenceTripleBlockWidth datum) by
            omega,
        induction (start + directFinalOccurrenceTripleBlockWidth datum)]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Stable indexing of the flat grouped query stream can be regrouped into
occurrence blocks whose global starts are exactly the scaled prefix sums used
by the routed-incidence key construction. -/
theorem
    directSourceFinalGroupedVariableIncidencePrefixQueries_zipIdx_eq_occurrenceBlocks
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).zipIdx =
      (List.zipWith
        (fun blockStart pair =>
          (groupedVariableIncidencePrefixQueryBlock pair).zipIdx
            (3 * blockStart))
        (directSourceFinalGroupedOccurrenceTripleBlockStarts
          decider symbols)
        (directSourceFinalGroupedVariableFanSlots decider symbols)).flatten := by
  unfold directSourceFinalGroupedVariableIncidencePrefixQueries
    directSourceFinalGroupedOccurrenceTripleBlockStarts
    directSourceFinalGroupedOccurrenceTripleBlockWidths PrefixSums.starts
  simpa using zipIdx_occurrenceBlocks 0
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalGroupedOccurrenceData decider symbols)
    (directSourceFinalGroupedVariableFanSlotKinds decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
