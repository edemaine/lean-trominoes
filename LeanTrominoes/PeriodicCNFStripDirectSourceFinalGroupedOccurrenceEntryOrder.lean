/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceHorizontalOrder
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanCountHorizontalSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntryIndices

/-! # Direct regrouping follows the canonical source occurrence entries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance groupedEntryOrderStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- The actual normalized source inherits the verified numeric occurrence
bound through the complete atom-identity correspondence. -/
theorem directSourceFinalNormalizedAtom_count_le_three
    (symbols : List encoding.Γ) (atom : RoutedVariable)
    (member : atom ∈ (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences) :
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.count atom ≤ 3 := by
  obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
  rw [← directSourceFinalAtomIdentityCodes_count_eq_normalized decider symbols index atom lookup]
  exact directSourceFinalAtomIdentityCodes_count_le_three decider symbols _

/-- Every recovered index appears in the exact canonical atom/slot entry
order used by the horizontal source assembly. -/
theorem directSourceFinalGroupedOccurrenceIndices_eq_occurrenceEntries
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceIndices decider symbols =
      (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
        (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase) := by
  rw [directSourceFinalGroupedOccurrenceIndices_eq_horizontal]
  exact (occurrenceEntries_map_index_eq_groupedIndices _ (fun atom member => by
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      directSourceFinalNormalizedAtom_count_le_three decider symbols atom member)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
