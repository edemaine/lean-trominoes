/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeFamilies
import LeanTrominoes.RetainedAngularFanFinalDeduplicatedClauseShape

/-! # Shape of final direct-source duplicate-free clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseShapeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalClauseShapeVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every final duplicate-free direct-source clause is nonempty. -/
theorem directSource_deduplicatedClauses_nonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols),
      clause ≠ [] := by
  apply deduplicatedClauses_nonempty_of_source
  rw [directSourceFormula_eq_threeSATThree]
  exact
    PeriodicThreeSATThree.formula_clausesNonempty
      (PeriodicThreeCNF.formula
        (PolySpaceCompiler.formulaOfSymbols decider symbols))
      (PeriodicThreeCNF.formula_clausesNonempty _
        (formulaOfSymbols_clauses_nonempty decider symbols))

/-- Every final duplicate-free direct-source clause has width at most
three. -/
theorem directSource_deduplicatedClauses_widthAtMostThree
    (symbols : List encoding.Γ) :
    ∀ clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols),
      clause.length ≤ 3 := by
  apply deduplicatedClauses_widthAtMostThree
  rw [directSourceFormula_eq_threeSATThree]
  exact
    PeriodicThreeSATThree.formula_widthAtMostThree
      (PeriodicThreeCNF.formula_widthAtMostThree
        (PolySpaceCompiler.formulaOfSymbols decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
