/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceEntryOrder

/-! # Unique compiled keys name the actual horizontal occurrence entries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

private theorem activeOccurrence_rank_lt_count
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (entry : Variable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries source) :
    entry.2.index < source.variableOccurrences.count entry.1 := by
  obtain ⟨tagged, lookup⟩ := occurrenceAt_exists_of_entry_mem source entry member
  unfold occurrenceAt PeriodicOneInThreeToThreeDM.occurrenceAt at lookup
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  simpa only [PeriodicOneInThreeToThreeDM.occurrencesOf_length] using bound

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The compiled key at an actual horizontal occurrence's presentation index.
Only active entries are used by the element-code interpretation. -/
def directSourceFinalHorizontalOccurrenceKey
    (symbols : List encoding.Γ) (entry : RoutedVariable × OccurrenceSlot) : Nat :=
  (directSourceFinalOccurrenceCandidateKeys decider symbols).getD
    (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry) 0

/-- Reading the candidate key at each recovered position inverts regrouping. -/
theorem directSourceFinalGroupedOccurrenceIndices_map_candidateKey
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        (fun index => (directSourceFinalOccurrenceCandidateKeys
          decider symbols).getD index 0) =
      directSourceFinalUniqueFanQueryKeys decider symbols := by
  rw [directSourceFinalGroupedOccurrenceIndices_eq_map_alignedDatum, List.map_map]
  conv_rhs => rw [← List.map_id (directSourceFinalUniqueFanQueryKeys decider symbols)]
  apply List.map_congr_left
  intro key member
  dsimp only [Function.comp_def, id_eq]
  have covered := directSourceFinalUniqueFanQueryKey_mem_candidateKeys
    decider symbols key member
  unfold directSourceFinalOccurrenceCandidateIndices UnaryFieldRange.values
  rw [UnaryKeyedValueLookup.alignedDatum_range _ _ covered]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_idxOf covered, Option.getD_some]

/-- Unique keys follow exactly the actual source entry order, so the same
key function can name elements in both canonical and incidence columns. -/
theorem directSourceFinalUniqueFanQueryKeys_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalUniqueFanQueryKeys decider symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
        (directSourceFinalHorizontalOccurrenceKey decider symbols) := by
  rw [← directSourceFinalGroupedOccurrenceIndices_map_candidateKey,
    directSourceFinalGroupedOccurrenceIndices_eq_occurrenceEntries, List.map_map]
  unfold directSourceFinalHorizontalOccurrenceKey
  simp only [Function.comp_def]

/-- Distinct active source entries have distinct compiled keys. -/
theorem directSourceFinalHorizontalOccurrenceKey_injective_on_entries
    (symbols : List encoding.Γ)
    (first second : RoutedVariable × OccurrenceSlot)
    (firstMember : first ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase)
    (secondMember : second ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase)
    (equal : directSourceFinalHorizontalOccurrenceKey decider symbols first =
      directSourceFinalHorizontalOccurrenceKey decider symbols second) :
    first = second := by
  have unique := directSourceFinalUniqueFanQueryKeys_nodup decider symbols
  rw [directSourceFinalUniqueFanQueryKeys_eq_horizontal] at unique
  exact List.inj_on_of_nodup_map unique firstMember secondMember equal


/-- Any genuine occurrence of the same atom supplies the common identity
base; the active slot supplies its own stable rank. This also applies when
naming the cyclic successor from the current occurrence's identity. -/
theorem directSourceFinalHorizontalOccurrenceKey_eq_base_rank
    (symbols : List encoding.Γ) (index : Nat) (atom : RoutedVariable)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom)
    (slot : OccurrenceSlot)
    (member : (atom, slot) ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase) :
    directSourceFinalHorizontalOccurrenceKey decider symbols (atom, slot) =
      (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 * 3 + slot.index := by
  have rankLt : slot.index < (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.count atom := by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      activeOccurrence_rank_lt_count (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase (atom, slot) member
  have keyMember : (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 * 3 + slot.index ∈
      directSourceFinalOccurrenceCandidateKeys decider symbols := by
    rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
    apply StableOccurrenceRanks.candidateKey_mem_of_rank_lt_count
    rw [directSourceFinalAtomIdentityCodes_count_eq_normalized decider symbols index atom atomLookup]
    exact rankLt
  have keyIndex := directSourceFinalOccurrenceCandidateKeys_idxOf_rank_normalized
    decider symbols index atom atomLookup slot.index rankLt
  unfold directSourceFinalHorizontalOccurrenceKey occurrenceEntryIndex
  dsimp only [Prod.fst, Prod.snd]
  simp only [List.idxsOf, Bool.beq_eq_decide_eq] at keyIndex ⊢
  rw [← keyIndex]
  exact congrArg (fun value : Option Nat => value.getD 0) (List.getElem?_idxOf keyMember)

end LeanTrominoes.PeriodicCNFStripReduction

end
