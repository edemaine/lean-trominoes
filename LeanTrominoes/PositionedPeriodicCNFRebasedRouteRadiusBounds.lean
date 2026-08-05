import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds
import LeanTrominoes.RetainedRayRasterizationCorridor

/-!
# Radius criteria for rebased incidence-route halo bounds

A rebased route starts at its variable representative.  If that
representative is in the fundamental square and every route point is at
coordinate distance at most one period from it, then the complete route is
automatically in the open one-period halo.  This module packages that small
arithmetic bridge in the form used by the final Figure 9 coordinate proof.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PeriodicGridDrawing

/-- A point within one period, coordinatewise, of a fundamental-square
center lies in the open one-period halo. -/
theorem positionInExpandedSquare_of_withinCoordinateRadius
    (drawing : PeriodicGridDrawing)
    {radius : Nat} {center point : Cell}
    (centerInside : drawing.PositionInFundamentalSquare center)
    (radiusLe : radius ≤ drawing.gridSize)
    (bounded : WithinCoordinateRadius radius center point) :
    drawing.PositionInExpandedSquare point := by
  have horizontalAbsolute :
      |point.1 - center.1| ≤ (radius : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast bounded.1
  have verticalAbsolute :
      |point.2 - center.2| ≤ (radius : Int) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast bounded.2
  have horizontal := (abs_le.mp horizontalAbsolute)
  have vertical := (abs_le.mp verticalAbsolute)
  have radiusLeInt : (radius : Int) ≤ drawing.gridSize := by
    exact_mod_cast radiusLe
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  simp only [PositionInFundamentalSquare] at centerInside
  simp only [PositionInExpandedSquare]
  omega

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- Every point of every rebased genuine incidence route is within one
physical period, coordinatewise, of that incidence's variable prototype. -/
def PlanarIncidencePresentation.RebasedRoutePointsWithinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) : Prop :=
  ∀ tagged ∈
      (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
    ∀ point ∈ presentation.variableToClauseRoute tagged.1,
      WithinCoordinateRadius placement.period
        (placement.position tagged.1.literal.atom) point

/-- The variable-centered one-period radius criterion implies the exact
rebased-route halo bound consumed by ribbon thickening. -/
theorem PlanarIncidencePresentation.rebasedRoutePointsInExpandedSquare_of_withinVariablePeriod
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement)
    (bounds : presentation.RebasedRoutePointsWithinVariablePeriod) :
    presentation.RebasedRoutePointsInExpandedSquare := by
  intro tagged taggedMember point pointMember
  let drawing :=
    incidenceDrawing source placement presentation.routes
  have taggedEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase taggedMember
  have targetMember :=
    (PeriodicCNF.incidenceGraph_isWellFormed source.erase).2
      tagged.1.edge (List.fst_mem_of_mem_zipIdx taggedEdgeMember) |>.2
  have variableMember :
      CNFVertex.variable tagged.1.literal.atom ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge]
      using targetMember
  have variablePositionMember :=
    incidenceDrawing_vertexPosition_mem_of_compatible
      source placement presentation.routes presentation.compatible
      variableMember
  have variablePositionEq :=
    incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes variableMember
  have variableInside :=
    presentation.compatible.2.2.2.2.1 _ variablePositionMember
  rw [variablePositionEq] at variableInside
  change drawing.PositionInFundamentalSquare
      (placement.position tagged.1.literal.atom) at variableInside
  apply
    PeriodicGridDrawing.positionInExpandedSquare_of_withinCoordinateRadius
      drawing variableInside
  · simpa [drawing] using
      (incidenceDrawing_gridSize source placement presentation.routes
        presentation.periodPositive).symm.le
  · exact bounds tagged taggedMember point pointMember

end PositionedPeriodicCNF
end LeanTrominoes
