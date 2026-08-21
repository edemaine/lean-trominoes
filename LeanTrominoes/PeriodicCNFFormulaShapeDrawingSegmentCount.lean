/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileOccurrenceShapeData
import LeanTrominoes.PeriodicCNFIncidenceDrawingSegmentCount

/-! # Drawing segment counts from finite CNF formula shapes -/

namespace LeanTrominoes
namespace PeriodicCNF

open UnaryProgramClauseProfile
open PeriodicOrthocrossing

/-- The exact drawing-segment statement associated with a finite formula
shape.  Naming the proposition lets large direct compilers reuse it without
re-elaborating the equality at every specialization boundary. -/
def FormulaShape.DrawingSegmentCountStatement
    {Variable : Type} [DecidableEq Variable]
    (shape : List FormulaShape.Token)
    (formula : PeriodicCNF Variable) : Prop :=
  (drawing formula.incidenceGraph).indexedSegments.length =
    ((FormulaShape.clauseProfiles shape).map
      ClauseProfile.routeSegmentCount).sum +
      2 * FormulaShape.variableCount shape

/-- A finite shape that records the exact clause profiles and distinct-variable
count determines the exact number of routed incidence-drawing segments. -/
theorem incidenceDrawing_indexedSegments_length_of_shape
    {Variable : Type} [DecidableEq Variable]
    (shape : List FormulaShape.Token)
    (formula : PeriodicCNF Variable)
    (correct :
      (FormulaShape.clauseProfiles shape).map ClauseProfile.literals =
          formula.clauses.map
            ClauseProfileOccurrenceSplit.literalProfiles ∧
        FormulaShape.variableCount shape =
          formula.variableOccurrences.dedup.length)
    (forward : formula.IsForwardLocal)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (exact : ∀ atom ∈ formula.variableOccurrences.dedup,
      formula.variableOccurrences.count atom = 3) :
    (drawing formula.incidenceGraph).indexedSegments.length =
      ((FormulaShape.clauseProfiles shape).map
        ClauseProfile.routeSegmentCount).sum +
        2 * FormulaShape.variableCount shape := by
  rw [incidenceDrawing_indexedSegments_length_of_profiles
    (FormulaShape.clauseProfiles shape) formula
    correct.1 forward degree exact]
  rw [correct.2]

/-- Predicate-packaged form of
`incidenceDrawing_indexedSegments_length_of_shape`. -/
theorem drawingSegmentCountStatement_of_shape
    {Variable : Type} [DecidableEq Variable]
    (shape : List FormulaShape.Token)
    (formula : PeriodicCNF Variable)
    (correct :
      (FormulaShape.clauseProfiles shape).map ClauseProfile.literals =
          formula.clauses.map
            ClauseProfileOccurrenceSplit.literalProfiles ∧
        FormulaShape.variableCount shape =
          formula.variableOccurrences.dedup.length)
    (forward : formula.IsForwardLocal)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (exact : ∀ atom ∈ formula.variableOccurrences.dedup,
      formula.variableOccurrences.count atom = 3) :
    FormulaShape.DrawingSegmentCountStatement shape formula := by
  exact incidenceDrawing_indexedSegments_length_of_shape
    shape formula correct forward degree exact

end PeriodicCNF
end LeanTrominoes
