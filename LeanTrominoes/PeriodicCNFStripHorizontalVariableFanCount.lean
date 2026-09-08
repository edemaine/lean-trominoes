/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCountPredCompiler
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans

/-! # Source fan counts are saturated occurrence multiplicities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

/-- Every occurring source variable uses the same saturated count predecessor
as the direct finite fan assembler. -/
theorem sourceVariableRibbonCountPred_eq_boundedCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (positive : 0 < source.variableOccurrences.count atom) :
    sourceVariableRibbonCountPred source atom =
      BoundedPositiveCountPreds.boundedPositiveCountPred (source.variableOccurrences.count atom) := by
  rw [← PeriodicOneInThreeToThreeDM.occurrencesOf_length] at positive ⊢
  unfold sourceVariableRibbonCountPred usedSlots occurrenceAt PeriodicOneInThreeToThreeDM.occurrenceAt
  generalize PeriodicOneInThreeToThreeDM.occurrencesOf source atom = occurrences at positive ⊢
  cases occurrences with
  | nil => simp at positive
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest => rfl

end LeanTrominoes.PeriodicCNFStripReduction
