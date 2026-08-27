/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineSourceTailRecordData
import LeanTrominoes.PeriodicCNFStripDirectFigureNinePolarityRouteTailData

/-! # Direct flat Figure 9 source-tail clause records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance
    directFigureNinePolarityTailRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFigureNinePolarityTailRecordDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Canonical flat clause input for the retained Figure 9 source generated
directly by one guarded PSPACE source-symbol word. -/
def directFigureNinePolarityRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  PeriodicCNF.FormulaShapeRetainedFigureNineSourceTailRecord.recordTokens
    (directSourceFormula decider symbols)

/-- The fixed bounded batch expander reconstructs the exact direct retained
header/tail record stream. -/
@[simp] theorem batchedRecords_directFigureNinePolarityRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (directFigureNinePolarityRouteTailRecordTokens decider symbols) =
      directFigureNinePolarityRouteTailRecords decider symbols := by
  unfold directFigureNinePolarityRouteTailRecordTokens
    directFigureNinePolarityRouteTailRecords
  exact
    PeriodicCNF.FormulaShapeRetainedFigureNineSourceTailRecord.batchedRecords_recordTokens
      (directSourceFormula decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
