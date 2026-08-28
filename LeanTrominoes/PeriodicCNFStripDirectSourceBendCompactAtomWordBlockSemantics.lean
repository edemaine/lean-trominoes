/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendCompactAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceBendCompactAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordFamilies

/-! # Direct compact bend stream agrees with the final bend-family block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBendCompactBlockSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directBendCompactBlockSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Delimited target carrying exactly the bend-family compact block. -/
def directSourceFinalCompactBendAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  ⟨directSourceFinalCompactBendAtomWordBlock decider symbols⟩

/-- The compiled descriptor-square bend stream is exactly the semantic bend
block of the final compact occurrence column. -/
theorem directSourceBendCompactAtomWords_eq_finalBlock
    (symbols : List encoding.Γ) :
    directSourceBendCompactAtomWords decider symbols =
      directSourceFinalCompactBendAtomWords decider symbols := by
  unfold directSourceBendCompactAtomWords
    directSourceFinalCompactBendAtomWords
    directSourceFinalCompactBendAtomWordBlock
    directThreeCNFSourceFormula
    directSourceFinalCompactAtomWord
  rw [directSourceFormula_eq_threeSATThree]
  dsimp only
  apply congrArg DelimitedBinaryWords.Input.mk
  rw [← List.flatMap_assoc]
  exact numericRouteDescriptors_bendCompactAtomWords_eq_normalizedLinks
    (PeriodicThreeSATThree.formula
      (directThreeCNFSourceFormula decider symbols))
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord
      (PeriodicThreeSATThree.formula
        (directThreeCNFSourceFormula decider symbols)))

end PeriodicCNFStripReduction
end LeanTrominoes

end
