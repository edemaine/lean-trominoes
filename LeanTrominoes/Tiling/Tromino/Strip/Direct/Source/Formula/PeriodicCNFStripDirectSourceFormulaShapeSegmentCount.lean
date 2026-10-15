/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaShapeProfileSegmentCount
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaShapeNamedVariableCount
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeDrawingSegmentCount

/-! # Direct formula-shape segment counts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable local instance directSourceShapeSegmentCountVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compact direct formula shape recovers the exact number of routed
segments in the canonical incidence drawing. -/
theorem directSourceFormulaShape_routedSegmentCount_eq
    (symbols : List encoding.Γ) :
    FormulaShape.routedSegmentCount
        (directSourceFormulaShape decider symbols) =
      (drawing
        (directSourceFormula decider symbols).incidenceGraph).indexedSegments.length := by
  unfold FormulaShape.routedSegmentCount
  rw [directSourceFormulaShape_variableCount_eq_distinct decider symbols]
  rw [directSourceFormulaShape_drawingSegments_eq_profileCount decider symbols]

end PeriodicCNFStripReduction
end LeanTrominoes

end
