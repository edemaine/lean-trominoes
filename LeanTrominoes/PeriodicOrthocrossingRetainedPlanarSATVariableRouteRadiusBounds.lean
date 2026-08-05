import LeanTrominoes.OrthogonalPolylineCoordinateRadiusBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierRouteBounds

/-!
# Variable-centered bounds for retained planar-SAT routes

The periodic rebase of an incidence route cancels the finite occurrence
translate at its variable endpoint.  The geometric input needed for that
cancellation is local: every point of a retained finite component route is
within one physical period, coordinatewise, of that route's variable
endpoint.  Non-carrier components fit in one `20 × 20` macrocell; carrier
lenses fit in a narrow rectangle whose axial span is strictly below one
period.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Two points in the same retained non-carrier macrocell are within one
physical planar-SAT period of each other. -/
private theorem within_period_of_in_same_planarSATMacrocell
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {center first second : Cell}
    (firstInside : InPlanarSATMacrocell center first)
    (secondInside : InPlanarSATMacrocell center second) :
    WithinCoordinateRadius
      (drawingPeriodicPlanarSATPlacement formula).period
      first second := by
  rw [withinCoordinateRadius_iff_abs_le]
  have gridPositive :
      0 < drawingGridSize (PeriodicCNF.incidenceGraph formula) :=
    drawingGridSize_pos _
  unfold InPlanarSATMacrocell planarSATMacrocellRouteLower
    planarSATMacrocellRouteUpper InClosedGridRectangle at
      firstInside secondInside
  simp only [drawingPeriodicPlanarSATPlacement,
    PeriodicVariablePlacement.period, Cell.add, Cell.scale]
  norm_num [planarMacroScale] at firstInside secondInside ⊢
  constructor <;> apply abs_le.mpr <;> omega

/-- Any point of a retained finite planar-SAT incidence route is within one
physical period of that incidence's displayed variable endpoint. -/
theorem metadata_localRoutePoint_within_variablePeriod
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex) :
    WithinCoordinateRadius
      (drawingPeriodicPlanarSATPlacement formula).period
      (drawingPlanarSATVariablePosition formula literal.1) point := by
  have clauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  have routesMatch :=
    metadata.retainedLocalDrawingRoutesMatch
      wellFormed degree isLocal valid
  have endpoints :=
    (metadata.source.incidenceDrawing formula).physicalRoutesMatch
      routesMatch metadata.clause metadata.source.localClauseIndex
      clauseMember literal literalIndex literalMember
  rw [DrawingPlanarSATClauseSource.incidenceDrawing_variablePosition]
    at endpoints
  have endpointMember :
      drawingPlanarSATVariablePosition formula literal.1 ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex :=
    mem_of_getLast?_eq_some endpoints.2
  by_cases carrier :
      ∃ link, metadata.source.component = .carrier link
  · rcases carrier with ⟨link, componentEq⟩
    rcases metadata with ⟨clause, source⟩
    rcases source.exists_eq_carrier_of_component_eq
        link componentEq with
      ⟨localClauseIndex, sourceEq⟩
    subst source
    have linkMember :
        link ∈ retainedDrawingCompleteCarrierLinks
          (PeriodicCNF.incidenceGraph formula) := by
      exact valid.1
    have pointInside :=
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
        wellFormed degree isLocal linkMember).of_members
          clauseMember literalMember pointMember
    have endpointInside :=
      (retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
        wellFormed degree isLocal linkMember).of_members
          clauseMember literalMember endpointMember
    have span :=
      retainedDrawingCompleteCarrierLink_position_span_lt_period
        wellFormed degree isLocal linkMember
    have periodPositive :
        2 < planarMacroScale *
          drawingGridSize (PeriodicCNF.incidenceGraph formula) := by
      have gridPositive :
          0 < drawingGridSize (PeriodicCNF.incidenceGraph formula) :=
        drawingGridSize_pos _
      norm_num [planarMacroScale] at gridPositive ⊢
      omega
    rw [withinCoordinateRadius_iff_abs_le]
    unfold drawingCompleteCarrierLinkRectangleLower
      drawingCompleteCarrierLinkRectangleUpper
      InClosedGridRectangle at pointInside endpointInside
    simp only [drawingPeriodicPlanarSATPlacement,
      PeriodicVariablePlacement.period]
    by_cases horizontal : link.first.isHorizontal = true
    · rw [if_pos horizontal] at pointInside endpointInside span
      simp only [horizontal, if_true] at pointInside endpointInside
      constructor <;> apply abs_le.mpr <;> omega
    · rw [if_neg horizontal] at pointInside endpointInside span
      have horizontalFalse : link.first.isHorizontal = false :=
        Bool.eq_false_of_not_eq_true horizontal
      simp only [horizontalFalse, Bool.false_eq_true, if_false]
        at pointInside endpointInside
      constructor <;> apply abs_le.mpr <;> omega
  · rcases metadata.source.component.exists_macrocellCenter_of_not_carrier
        formula carrier with
      ⟨center, centerEq⟩
    have originalValid : metadata.Valid formula :=
      metadata.valid_of_retainedValid_of_not_carrier valid carrier
    have pointInside :=
      metadata.localRoutePoints_inPlanarSATMacrocell
        wellFormed degree isLocal originalValid center centerEq
        literalMember pointMember
    have endpointInside :=
      metadata.localRoutePoints_inPlanarSATMacrocell
        wellFormed degree isLocal originalValid center centerEq
        literalMember endpointMember
    exact within_period_of_in_same_planarSATMacrocell
      formula endpointInside pointInside

end PeriodicOrthocrossing
end LeanTrominoes
