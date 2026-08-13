/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionScaling
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionVariableRouteOrder
import LeanTrominoes.RetainedAngularFanFinalCoordinatedTerminalDirections
import LeanTrominoes.RetainedAngularFanFinalNormalizedVariableRouteOrder

/-!
# Variable route order after Figure 9 source clearance

Clockwise sorting at clauses does not disturb the occurrence order at
variables.  The subsequent factor-two clearance scale and verified loop
erasure preserve every variable-side terminal direction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

/-- The clockwise clause presentation retains the source drawing's variable
occurrence order. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
        source) := by
  exact
    PositionedPeriodicCNF.orderCanonicalRoutesByClauseDirection_variableRoutesInOccurrenceOrder
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

/-- The factor-two source clearance and its final loop erasure retain
variable occurrence order. -/
theorem
    retainedFigureNineClearanceIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearanceIncidenceRoutes source) := by
  let clockwiseFormula :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source
  let clockwiseRoutes :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source
  have scaledOrder :
      (clockwiseFormula.scale
        retainedFigureNineSourceClearanceFactor).VariableRoutesInOccurrenceOrder
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedFigureNineSourceClearanceFactor clockwiseRoutes) :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).scale
        retainedFigureNineSourceClearanceFactor
        retainedFigureNineSourceClearanceFactor_pos
  change
    (clockwiseFormula.scale
      retainedFigureNineSourceClearanceFactor).VariableRoutesInOccurrenceOrder
      (PositionedPeriodicCNF.normalizeOrthogonalIncidenceRoutes
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedFigureNineSourceClearanceFactor clockwiseRoutes))
  apply
    scaledOrder.normalizeOrthogonalIncidenceRoutes_of_lastNotInDropLast
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
      ⟨sourceClause, sourceClauseMember, clauseEq⟩
    subst clause
    have sourceLiteralMember :
        (literal, literalIndex) ∈ sourceClause.literals.zipIdx := by
      simpa using literalMember
    simpa [PositionedPeriodicCNF.scaleIncidenceRoutes,
      LeanTrominoes.scalePolyline] using
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
      ⟨sourceClause, sourceClauseMember, clauseEq⟩
    subst clause
    have sourceLiteralMember :
        (literal, literalIndex) ∈ sourceClause.literals.zipIdx := by
      simpa using literalMember
    have sourceOrthogonal :=
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2
    simpa [PositionedPeriodicCNF.scaleIncidenceRoutes] using
      sourceOrthogonal.scalePolyline
        retainedFigureNineSourceClearanceFactor_pos
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    rcases exists_clockwiseClause_of_clearanceClause_mem clauseMember with
      ⟨sourceClause, sourceClauseMember, clauseEq⟩
    subst clause
    have sourceLiteralMember :
        (literal, literalIndex) ∈ sourceClause.literals.zipIdx := by
      simpa using literalMember
    have sourceOrthogonal :=
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2
    have sourceFresh :=
      AxisDirection.lastNotInDropLast_unitSubdividePolyline_of_simple
        sourceOrthogonal
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_isSimple
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
    simpa [PositionedPeriodicCNF.scaleIncidenceRoutes] using
      sourceFresh.unitSubdividePolyline_scalePolyline
        retainedFigureNineSourceClearanceFactor_pos sourceOrthogonal

end PeriodicOrthocrossing
end LeanTrominoes
