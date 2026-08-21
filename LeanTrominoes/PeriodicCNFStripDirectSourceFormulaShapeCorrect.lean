/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeSemantics

/-! # Formula-shape correctness for the named direct source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceFormulaShapeCorrectStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The existing direct shape theorem, stated through the compact named source
formula used by the segment compiler. -/
theorem directSourceFormulaShape_correct_named
    (symbols : List encoding.Γ) :
    (FormulaShape.clauseProfiles
        (directSourceFormulaShape decider symbols)).map
          ClauseProfile.literals =
        (directSourceFormula decider symbols).clauses.map
          ClauseProfileOccurrenceSplit.literalProfiles ∧
      FormulaShape.variableCount
          (directSourceFormulaShape decider symbols) =
        (directSourceFormula decider symbols).variableOccurrences.dedup.length := by
  exact directSourceFormulaShape_correct decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes
