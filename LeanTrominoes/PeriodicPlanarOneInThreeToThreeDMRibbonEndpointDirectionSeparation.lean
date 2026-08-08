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

/-- Distinct active source routes cannot leave adjacent variable positions
through the same unit edge in opposite directions.  This is the source-level
obstruction corresponding to the sole adjacent variable-fan contact
classified by the finite ribbon tables. -/
theorem occurrenceSourceVariableDirections_not_facing
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second) :
    ∀ direction, direction.IsGenuine →
      Cell.sub (placement.position second.1.1)
          (placement.position first.1.1) ≠ direction.step ∨
        occurrenceSourceVariableDirection
            presentation.toPlanarIncidencePresentation first ≠ direction ∨
        occurrenceSourceVariableDirection
            presentation.toPlanarIncidencePresentation second ≠
          direction.opposite := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstData := occurrenceSpliceData planar first
  let secondData := occurrenceSpliceData planar second
  have firstAtom : firstData.tagged.1.atom = first.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase first.1.1 first.1.2 firstData.tagged
      firstData.occurrenceLookup).2
  have secondAtom : secondData.tagged.1.atom = second.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase second.1.1 second.1.2 secondData.tagged
      secondData.occurrenceLookup).2
  have firstHead :
      (occurrenceSourceRoute planar first).head? =
        some (placement.position first.1.1) := by
    simpa [occurrenceSourceRoute, firstData, firstAtom] using
      firstData.routeHead
  have secondHead :
      (occurrenceSourceRoute planar second).head? =
        some (placement.position second.1.1) := by
    simpa [occurrenceSourceRoute, secondData, secondAtom] using
      secondData.routeHead
  intro direction genuine
  by_cases offsetDifferent :
      Cell.sub (placement.position second.1.1)
          (placement.position first.1.1) ≠ direction.step
  · exact Or.inl offsetDifferent
  · right
    have offsetEqual :
        Cell.sub (placement.position second.1.1)
            (placement.position first.1.1) = direction.step :=
      not_ne_iff.mp offsetDifferent
    have adjacent :
        placement.position second.1.1 =
          Cell.add (placement.position first.1.1) direction.step := by
      calc
        placement.position second.1.1 =
            Cell.add (placement.position first.1.1)
              (Cell.sub (placement.position second.1.1)
                (placement.position first.1.1)) := by
          rcases placement.position first.1.1 with ⟨firstX, firstY⟩
          rcases placement.position second.1.1 with ⟨secondX, secondY⟩
          simp [Cell.add, Cell.sub]
        _ = Cell.add (placement.position first.1.1) direction.step := by
          rw [offsetEqual]
    have separated :=
      polylineFirstDirections_not_facing_of_routesAvoidEachOther
        (occurrenceSourceRoute_length planar first)
        (occurrenceSourceRoute_length planar second)
        firstHead secondHead genuine adjacent
        (occurrenceSourceRoutes_avoidEachOther_of_ne
          presentation different)
    simpa [occurrenceSourceVariableDirection_eq_sourceRoute]
      using separated

/-- Distinct incidences of one clause orbit enter every translated copy of
that clause in different directions.  Their stored routes share the
canonical clause endpoint; reversing and independently rebasing those routes
changes neither incoming direction. -/
theorem occurrenceSourceClauseDirections_ne_of_same_clause
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    {first second : ActiveOccurrenceEntry source.erase}
    (different : first ≠ second)
    (sameClause :
      let planar := presentation.toPlanarIncidencePresentation
      let firstData := occurrenceSpliceData planar first
      let secondData := occurrenceSpliceData planar second
      firstData.indexed.1.clauseIndex =
        secondData.indexed.1.clauseIndex) :
    occurrenceSourceClauseDirection
        presentation.toPlanarIncidencePresentation first ≠
      occurrenceSourceClauseDirection
        presentation.toPlanarIncidencePresentation second := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstData := occurrenceSpliceData planar first
  let secondData := occurrenceSpliceData planar second
  let firstRoute :=
    planar.routes firstData.indexed.1.clauseIndex
      firstData.indexed.1.literalIndex
  let secondRoute :=
    planar.routes secondData.indexed.1.clauseIndex
      secondData.indexed.1.literalIndex
  have routeIndexDifferent :
      firstData.indexed.2 ≠ secondData.indexed.2 := by
    intro indexEqual
    have firstLookup :=
      (List.mem_zipIdx_iff_getElem?).mp firstData.indexedMember
    have secondLookup :=
      (List.mem_zipIdx_iff_getElem?).mp secondData.indexedMember
    have incidenceEqual :
        firstData.indexed.1 = secondData.indexed.1 := by
      rw [indexEqual] at firstLookup
      exact Option.some.inj (firstLookup.symm.trans secondLookup)
    have keyEqual :
        occurrenceSourceRouteKey planar first =
          occurrenceSourceRouteKey planar second := by
      change
        (firstData.indexed.2,
            PositionedPeriodicCNF.variableToClauseTranslate
              firstData.indexed.1) =
          (secondData.indexed.2,
            PositionedPeriodicCNF.variableToClauseTranslate
              secondData.indexed.1)
      exact Prod.ext indexEqual
        (congrArg
          PositionedPeriodicCNF.variableToClauseTranslate
          incidenceEqual)
    exact different
      (occurrenceSourceRouteKey_injective planar keyEqual)
  have sameStart : firstRoute.head? = secondRoute.head? := by
    have firstEndpoints :=
      planar.route_endpoints_of_tagged firstData.indexedMember
    have secondEndpoints :=
      planar.route_endpoints_of_tagged secondData.indexedMember
    calc
      firstRoute.head? =
          some
            (PositionedPeriodicCNF.incidenceVertexPositionAt
              source placement
                (.clause firstData.indexed.1.clauseIndex)) := by
        simpa [firstRoute] using firstEndpoints.1
      _ =
          some
            (PositionedPeriodicCNF.incidenceVertexPositionAt
              source placement
                (.clause secondData.indexed.1.clauseIndex)) := by
        rw [sameClause]
      _ = secondRoute.head? := by
        simpa [secondRoute] using secondEndpoints.1.symm
  have avoid :
      RoutesAvoidEachOther firstRoute secondRoute := by
    let drawing :=
      PositionedPeriodicCNF.incidenceDrawing
        source placement planar.routes
    have originalAvoid :=
      PeriodicGridDrawing.routeOccurrences_avoidEachOther
        (drawing := drawing)
        presentation.continuouslyPlanar
        presentation.endpointContacts
        (planar.route_zipIdx_mem_of_tagged firstData.indexedMember)
        (planar.route_zipIdx_mem_of_tagged secondData.indexedMember)
        (planar.route_length_ge_two_of_tagged firstData.indexedMember)
        (planar.route_length_ge_two_of_tagged secondData.indexedMember)
        (planar.route_orthogonal_of_tagged firstData.indexedMember)
        (planar.route_orthogonal_of_tagged secondData.indexedMember)
        (0, 0) (0, 0)
        (by simpa using routeIndexDifferent)
    have zeroTranslation :
        drawing.periodTranslation (0, 0) = (0, 0) := by
      simp [drawing, PeriodicGridDrawing.periodTranslation,
        Cell.scale]
    rw [zeroTranslation] at originalAvoid
    have mapZero (points : List Cell) :
        points.map (Cell.add (0, 0)) = points := by
      induction points with
      | nil => rfl
      | cons point rest induction =>
          simp [Cell.add, induction]
    rw [mapZero, mapZero] at originalAvoid
    simpa [firstRoute, secondRoute] using originalAvoid
  have firstDirectionsDifferent :
      AxisDirection.polylineFirstDirection firstRoute ≠
        AxisDirection.polylineFirstDirection secondRoute :=
    polylineFirstDirections_ne_of_routesAvoidEachOther
      (planar.route_length_ge_two_of_tagged
        firstData.indexedMember)
      (planar.route_length_ge_two_of_tagged
        secondData.indexedMember)
      (planar.route_orthogonal_of_tagged
        firstData.indexedMember)
      (planar.route_orthogonal_of_tagged
        secondData.indexedMember)
      sameStart avoid
  rw [occurrenceSourceClauseDirection_eq_storedRoute,
    occurrenceSourceClauseDirection_eq_storedRoute]
  exact fun equal =>
    firstDirectionsDifferent
      (AxisDirection.opposite_injective equal)

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
