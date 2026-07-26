import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirections
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceSeparation

/-!
# Separation of occurrence endpoint directions

Distinct active source routes cannot overlap immediately after a common
variable endpoint or immediately before a common clause endpoint.  This file
turns that continuous-separation fact into the finite cardinal-direction
constraints needed to choose noncrossing endpoint-fan templates.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Distinct active source routes with the same unitized initial point leave
that point in different cardinal directions. -/
theorem occurrenceSourceVariableDirections_ne_of_same_start
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second)
    (sameStart :
      (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).head? =
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).head?) :
    occurrenceSourceVariableDirection
        presentation.toPlanarIncidencePresentation first ≠
      occurrenceSourceVariableDirection
        presentation.toPlanarIncidencePresentation second := by
  let planar := presentation.toPlanarIncidencePresentation
  have firstNonempty :
      occurrenceSourceRoute planar first ≠ [] :=
    List.ne_nil_of_length_pos
      (lt_of_lt_of_le (by decide)
        (occurrenceSourceRoute_length planar first))
  have secondNonempty :
      occurrenceSourceRoute planar second ≠ [] :=
    List.ne_nil_of_length_pos
      (lt_of_lt_of_le (by decide)
        (occurrenceSourceRoute_length planar second))
  have originalSameStart :
      (occurrenceSourceRoute planar first).head? =
        (occurrenceSourceRoute planar second).head? := by
    calc
      (occurrenceSourceRoute planar first).head? =
          (occurrenceUnitSourceRoute planar first).head? := by
        rw [occurrenceUnitSourceRoute,
          AxisDirection.unitSubdividePolyline_head? firstNonempty]
      _ = (occurrenceUnitSourceRoute planar second).head? := by
        simpa [planar] using sameStart
      _ = (occurrenceSourceRoute planar second).head? := by
        rw [occurrenceUnitSourceRoute,
          AxisDirection.unitSubdividePolyline_head? secondNonempty]
  rw [occurrenceSourceVariableDirection_eq_sourceRoute,
    occurrenceSourceVariableDirection_eq_sourceRoute]
  exact
    polylineFirstDirections_ne_of_routesAvoidEachOther
      (occurrenceSourceRoute_length planar first)
      (occurrenceSourceRoute_length planar second)
      (occurrenceSourceRoute_orthogonal planar first)
      (occurrenceSourceRoute_orthogonal planar second)
      originalSameStart
      (occurrenceSourceRoutes_avoidEachOther_of_ne
        presentation different)

/-- Distinct active occurrences of one variable leave its source macrocell
in different cardinal directions. -/
theorem occurrenceSourceVariableDirections_ne_of_same_variable
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second)
    (sameVariable : first.1.1 = second.1.1) :
    occurrenceSourceVariableDirection
        presentation.toPlanarIncidencePresentation first ≠
      occurrenceSourceVariableDirection
        presentation.toPlanarIncidencePresentation second := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstData := occurrenceSpliceData planar first
  let secondData := occurrenceSpliceData planar second
  have firstAtom :
      firstData.tagged.1.atom = first.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase first.1.1 first.1.2 firstData.tagged
      firstData.occurrenceLookup).2
  have secondAtom :
      secondData.tagged.1.atom = second.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase second.1.1 second.1.2 secondData.tagged
      secondData.occurrenceLookup).2
  have sameStart :
      (occurrenceSourceRoute planar first).head? =
        (occurrenceSourceRoute planar second).head? := by
    calc
      (occurrenceSourceRoute planar first).head? =
          some (placement.position firstData.tagged.1.atom) := by
        simpa [occurrenceSourceRoute, firstData] using
          firstData.routeHead
      _ = some (placement.position secondData.tagged.1.atom) := by
        simp [firstAtom, secondAtom, sameVariable]
      _ = (occurrenceSourceRoute planar second).head? := by
        simpa [occurrenceSourceRoute, secondData] using
          secondData.routeHead.symm
  rw [occurrenceSourceVariableDirection_eq_sourceRoute,
    occurrenceSourceVariableDirection_eq_sourceRoute]
  exact
    polylineFirstDirections_ne_of_routesAvoidEachOther
      (occurrenceSourceRoute_length planar first)
      (occurrenceSourceRoute_length planar second)
      (occurrenceSourceRoute_orthogonal planar first)
      (occurrenceSourceRoute_orthogonal planar second)
      sameStart
      (occurrenceSourceRoutes_avoidEachOther_of_ne
        presentation different)

/-- Distinct active occurrences entering the same lifted clause endpoint do
so in different cardinal directions. -/
theorem occurrenceSourceClauseDirections_ne_of_same_target
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second)
    (sameTarget :
      let planar := presentation.toPlanarIncidencePresentation
      let firstData := occurrenceSpliceData planar first
      let secondData := occurrenceSpliceData planar second
      PositionedPeriodicCNF.variableToClauseTarget
          placement firstData.positionedClause firstData.tagged.1 =
        PositionedPeriodicCNF.variableToClauseTarget
          placement secondData.positionedClause secondData.tagged.1) :
    occurrenceSourceClauseDirection
        presentation.toPlanarIncidencePresentation first ≠
      occurrenceSourceClauseDirection
        presentation.toPlanarIncidencePresentation second := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstData := occurrenceSpliceData planar first
  let secondData := occurrenceSpliceData planar second
  have sameFinish :
      (occurrenceSourceRoute planar first).getLast? =
        (occurrenceSourceRoute planar second).getLast? := by
    calc
      (occurrenceSourceRoute planar first).getLast? =
          some (PositionedPeriodicCNF.variableToClauseTarget
            placement firstData.positionedClause
              firstData.tagged.1) := by
        simpa [occurrenceSourceRoute, firstData] using
          firstData.routeLast
      _ = some (PositionedPeriodicCNF.variableToClauseTarget
            placement secondData.positionedClause
              secondData.tagged.1) := by
        simpa [planar, firstData, secondData] using congrArg some sameTarget
      _ = (occurrenceSourceRoute planar second).getLast? := by
        simpa [occurrenceSourceRoute, secondData] using
          secondData.routeLast.symm
  rw [occurrenceSourceClauseDirection_eq_sourceRoute,
    occurrenceSourceClauseDirection_eq_sourceRoute]
  exact
    polylineLastDirections_ne_of_routesAvoidEachOther
      (occurrenceSourceRoute_length planar first)
      (occurrenceSourceRoute_length planar second)
      (occurrenceSourceRoute_orthogonal planar first)
      (occurrenceSourceRoute_orthogonal planar second)
      sameFinish
      (occurrenceSourceRoutes_avoidEachOther_of_ne
        presentation different)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
