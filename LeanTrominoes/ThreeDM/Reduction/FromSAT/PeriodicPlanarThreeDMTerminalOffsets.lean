/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMIncidenceClassification
import Mathlib.Tactic.IntervalCases

/-! # A clause terminal determines the offset of its routed incidence -/
namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM
set_option maxHeartbeats 1000000

theorem terminalGroup_injective_below_three {first second : Nat}
    (firstBound : first < 3) (secondBound : second < 3)
    (equal : terminalGroupOfLiteralIndex first = terminalGroupOfLiteralIndex second) : first = second := by
  interval_cases first <;> interval_cases second <;> simp [terminalGroupOfLiteralIndex] at equal ⊢

theorem occurrenceReverseOffset_eq_of_terminal_eq {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (width : source.WidthAtMost 3)
    {firstAtom secondAtom : V} {firstSlot secondSlot : OccurrenceSlot}
    (firstUsed : firstSlot ∈ usedSlots source firstAtom)
    (secondUsed : secondSlot ∈ usedSlots source secondAtom)
    (clauseEq : occurrenceClauseIndex source firstAtom firstSlot =
      occurrenceClauseIndex source secondAtom secondSlot)
    (groupEq : terminalGroupOfLiteralIndex (occurrenceLiteralIndex source firstAtom firstSlot) =
      terminalGroupOfLiteralIndex (occurrenceLiteralIndex source secondAtom secondSlot)) :
    occurrenceReverseOffset source firstAtom firstSlot = occurrenceReverseOffset source secondAtom secondSlot := by
  obtain ⟨first,firstLookup⟩ := exists_occurrenceAt_of_mem_usedSlots source firstAtom firstSlot firstUsed
  obtain ⟨second,secondLookup⟩ := exists_occurrenceAt_of_mem_usedSlots source secondAtom secondSlot secondUsed
  obtain ⟨firstIncidence,firstMember,firstEq⟩ := exists_incidenceWithMetadata_of_tagged_mem source first
    ((PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom source firstAtom firstSlot first firstLookup).1)
  obtain ⟨secondIncidence,secondMember,secondEq⟩ := exists_incidenceWithMetadata_of_tagged_mem source second
    ((PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom source secondAtom secondSlot second secondLookup).1)
  have firstBounds := (PeriodicCNF.mem_incidencesWithMetadata_iff source firstIncidence).mp firstMember
  have secondBounds := (PeriodicCNF.mem_incidencesWithMetadata_iff source secondIncidence).mp secondMember
  have firstBound : firstIncidence.literalIndex < 3 := lt_of_lt_of_le
    (List.snd_lt_of_mem_zipIdx firstBounds.2)
    (width _ (List.fst_mem_of_mem_zipIdx firstBounds.1))
  have secondBound : secondIncidence.literalIndex < 3 := lt_of_lt_of_le
    (List.snd_lt_of_mem_zipIdx secondBounds.2)
    (width _ (List.fst_mem_of_mem_zipIdx secondBounds.1))
  have clauses : firstIncidence.clauseIndex = secondIncidence.clauseIndex := by
    simpa only [occurrenceClauseIndex_of_occurrenceAt source firstAtom firstSlot first firstLookup,
      occurrenceClauseIndex_of_occurrenceAt source secondAtom secondSlot second secondLookup,
      ← firstEq, ← secondEq, incidenceTaggedOccurrence] using clauseEq
  have groups : terminalGroupOfLiteralIndex firstIncidence.literalIndex =
      terminalGroupOfLiteralIndex secondIncidence.literalIndex := by
    simpa only [occurrenceLiteralIndex_of_occurrenceAt source firstAtom firstSlot first firstLookup,
      occurrenceLiteralIndex_of_occurrenceAt source secondAtom secondSlot second secondLookup,
      ← firstEq, ← secondEq, incidenceTaggedOccurrence] using groupEq
  have incidenceEq := PeriodicCNF.incidence_eq_of_indices_eq source firstMember secondMember clauses
    (terminalGroup_injective_below_three firstBound secondBound groups)
  rw [occurrenceReverseOffset_of_occurrenceAt source firstAtom firstSlot first firstLookup,
    occurrenceReverseOffset_of_occurrenceAt source secondAtom secondSlot second secondLookup,
    ← firstEq, ← secondEq, incidenceEq]

theorem occurrenceReverseOffset_eq_of_elementIndex_eq {V : Type*} [DecidableEq V]
    {source : PeriodicCNF V} (width : source.WidthAtMost 3)
    {firstAtom secondAtom : V} {firstSlot secondSlot : OccurrenceSlot}
    (firstUsed : firstSlot ∈ usedSlots source firstAtom)
    (secondUsed : secondSlot ∈ usedSlots source secondAtom) (color : WireColor)
    (equal : routedOccurrenceElementIndex source firstAtom firstSlot color =
      routedOccurrenceElementIndex source secondAtom secondSlot color) :
    occurrenceReverseOffset source firstAtom firstSlot = occurrenceReverseOffset source secondAtom secondSlot := by
  have firstMembers := occurrence_clause_elements_mem source firstAtom firstSlot firstUsed
  cases color
  · have same := (RedElement.clauseTerminal.inj ((List.idxOf_inj firstMembers.1).mp equal))
    exact occurrenceReverseOffset_eq_of_terminal_eq width firstUsed secondUsed same.1 same.2
  · have same := (GreenElement.clauseTerminal.inj ((List.idxOf_inj firstMembers.2.1).mp equal))
    exact occurrenceReverseOffset_eq_of_terminal_eq width firstUsed secondUsed same.1 same.2
  · have same := (BlueElement.clauseTerminal.inj ((List.idxOf_inj firstMembers.2.2).mp equal))
    exact occurrenceReverseOffset_eq_of_terminal_eq width firstUsed secondUsed same.1 same.2

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
