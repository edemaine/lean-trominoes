/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanRankLookup
import LeanTrominoes.PeriodicCNFStripHorizontalVariableFanCount

/-! # Complete direct fan counts agree with the actual normalized source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFanCountHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- The numeric identity at a genuine incidence has exactly its actual
normalized source atom's total multiplicity. -/
theorem directSourceFinalAtomIdentityCodes_count_eq_normalized
    (symbols : List encoding.Γ) (index : Nat) (atom : RoutedVariable)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom) :
    (directSourceFinalAtomIdentityCodes decider symbols).count
        ((directSourceFinalAtomIdentityCodes decider symbols).getD index 0) =
      (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.count atom := by
  rw [horizontalSemanticNormalizedRibbonSource_variableOccurrences] at atomLookup ⊢
  obtain ⟨atomLt, atomEq⟩ := List.getElem?_eq_some_iff.mp atomLookup
  have codeLt : index < (directSourceFinalAtomIdentityCodes decider symbols).length := by
    rw [directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms]
    exact atomLt
  have counts := StableOccurrenceRanks.count_eq_of_partition
    (directSourceFinalAtomIdentityCodes decider symbols)
    (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences
    (directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms decider symbols)
    (directSourceFinalAtomIdentityCodes_partition_horizontal decider symbols) index codeLt
  simpa only [List.getD_eq_getElem _ _ codeLt, atomEq,
    List.count_eq_countP, Bool.beq_eq_decide_eq] using counts

/-- The count passed to the finite direct fan assembler is the actual
source variable fan's count predecessor. -/
theorem directSourceFinalVariableFan_countPred_eq_source
    (symbols : List encoding.Γ) (index : Nat) (atom : RoutedVariable)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom) :
    BoundedPositiveCountPreds.boundedPositiveCountPred
      ((directSourceFinalAtomIdentityCodes decider symbols).count
        ((directSourceFinalAtomIdentityCodes decider symbols).getD index 0)) =
      PeriodicPlanarOneInThreeToThreeDM.sourceVariableRibbonCountPred
        (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase atom := by
  rw [directSourceFinalAtomIdentityCodes_count_eq_normalized decider symbols index atom atomLookup]
  have positive : 0 < (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.count atom :=
    List.count_pos_iff.mpr (List.mem_iff_getElem?.mpr ⟨index, atomLookup⟩)
  have countEq := sourceVariableRibbonCountPred_eq_boundedCount
    (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase atom (by
        simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using positive)
  simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using countEq.symm

end LeanTrominoes.PeriodicCNFStripReduction

end
