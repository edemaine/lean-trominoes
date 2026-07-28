import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVertexPositions

/-!
# Compatibility of the final gauged incidence drawing

The complete retained periodic drawing has the graph-prescribed numbers of
vertices and routes, distinct vertex positions in the open fundamental
square, and exact periodically translated route endpoints.  These facts
assemble the `PeriodicGridDrawing.IsCompatible` certificate used by the
subsequent periodic planarity layer.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_vertexPositions_inSquare
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    ∀ position ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).vertexPositions,
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).PositionInFundamentalSquare position := by
  have periodPositive :
      0 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
    simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  intro position positionMem
  unfold
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
    PeriodicGridDrawing.PositionInFundamentalSquare
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)
    periodPositive]
  exact
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_incidenceVertexPositions_inSquare
      formula wellFormed degree isLocal clausesNonempty
      position positionMem

theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).IsCompatible
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).erase.incidenceGraph := by
  have periodPositive :
      0 <
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).period := by
    simpa [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  apply PositionedPeriodicCNF.deduplicatedIncidenceDrawing_isCompatible
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula)
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
    (PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDrawingPlanarSATLocalIncidenceRoutes formula))
  · exact
      PositionedPeriodicCNF.anchorNormalizedIncidenceRoutes_physicalRoutesMatch
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
        (retainedDrawingPlanarSATLocalIncidenceRoutes formula)
        (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_physicalRoutesMatch
          formula wellFormed degree isLocal)
  · exact periodPositive
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_incidenceVertexPositions_nodup
        formula wellFormed degree isLocal clausesNonempty
  · exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_vertexPositions_inSquare
        formula wellFormed degree isLocal clausesNonempty

end LeanTrominoes.PeriodicOrthocrossing
