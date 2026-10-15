/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalPeriodSize
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.Tiling.Tromino.Strip.Source.PeriodicCNFStripSourceExactGridSize

/-! # Exact orthocrossing scale of the direct PSPACE source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

attribute [local instance] sourceVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The complete orthocrossing scale is a fixed affine weight of the
postorder instruction program: one clause weight, five literal weights, and
seven fixed units for the forced root and the grid margin. -/
@[simp] theorem sourceOrthocrossingGridSize_formulaOfSymbols
    (symbols : List encoding.Γ) :
    sourceOrthocrossingGridSize
        (ProgramSource.formulaOfSymbols decider symbols) =
      16 *
        (TransitionProgram.clauseCount
            (ProgramSource.program decider symbols) +
          5 * TransitionProgram.literalCount
            (ProgramSource.program decider symbols) + 7) := by
  unfold sourceOrthocrossingGridSize
  rw [drawingGridSize_incidenceGraph_sourceFormula_of
      _ (formulaOfSymbols_sourceAdmissible decider symbols)
        (formulaOfSymbols_widthAtMostThree decider symbols),
    formulaOfSymbols_clauses_length,
    formulaOfSymbols_presentationLiteralCount]
  omega

end PeriodicCNFStripReduction
end LeanTrominoes
