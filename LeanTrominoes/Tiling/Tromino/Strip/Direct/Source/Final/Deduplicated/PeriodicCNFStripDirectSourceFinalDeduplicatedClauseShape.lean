/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Occurrence.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeFamilies
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Deduplicated.RetainedAngularFanFinalDeduplicatedClauseShape

/-! # Shape of final direct-source duplicate-free clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
        (ProgramSource.formulaOfSymbols decider symbols))
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
        (ProgramSource.formulaOfSymbols decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
