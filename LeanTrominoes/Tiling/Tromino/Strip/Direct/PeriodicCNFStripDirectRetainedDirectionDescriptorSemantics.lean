/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeRetainedFigureNineDirectionExact
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedDirectionDescriptorData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFormulaShapeData

/-! # Exact direct retained Figure 9 direction descriptors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directRetainedDirectionDescriptorSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The fixed finite clockwise lookup on the direct descriptor stream is
exactly the canonical retained Figure 9 source shape. -/
theorem directRetainedFigureNineDirectionShape_eq
    (symbols : List encoding.Γ) :
    FormulaShapeDirectionOrdering.shape
        (directRetainedFigureNineDirectionDescriptors decider symbols) =
      directRetainedFigureNineSourceShape decider symbols := by
  simpa only [directRetainedFigureNineDirectionDescriptors,
    directRetainedFigureNineSourceShape,
    FormulaShapeRetainedFigureNineDirection.shape] using
    FormulaShapeRetainedFigureNineDirection.shape_eq_sourceShape
      (sourceFormula (ProgramSource.formulaOfSymbols decider symbols))
      (sourceFormula_widthAtMostThree _)
      (sourceFormula_clausesNonempty _)

end PeriodicCNFStripReduction
end LeanTrominoes
