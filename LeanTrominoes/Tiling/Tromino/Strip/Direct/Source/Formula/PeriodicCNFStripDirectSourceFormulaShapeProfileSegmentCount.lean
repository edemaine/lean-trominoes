/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.PeriodicCNFIncidenceDrawingSegmentCount
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Distinct.PeriodicCNFStripDirectSourceDistinctVariableCountData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaShapeClauseProfileCorrect
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaExactOccurrencesNamed

/-! # Direct clause-profile drawing segment counts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable local instance directSourceProfileSegmentCountVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct shape's clause-profile contribution and source variable count
give the exact drawing segment count. -/
theorem directSourceFormulaShape_drawingSegments_eq_profileCount
    (symbols : List encoding.Γ) :
    (drawing
      (directSourceFormula decider symbols).incidenceGraph).indexedSegments.length =
      ((FormulaShape.clauseProfiles
        (directSourceFormulaShape decider symbols)).map
          ClauseProfile.routeSegmentCount).sum +
        2 * directSourceDistinctVariableCount decider symbols := by
  unfold directSourceDistinctVariableCount
  apply PeriodicCNF.incidenceDrawing_indexedSegments_length_of_profiles
  · exact directSourceFormulaShape_clauseProfiles_correct decider symbols
  · exact directSourceFormula_isForwardLocal decider symbols
  · exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  · exact directSourceFormula_variableOccurrences_count_eq_three_of_mem
      decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end
