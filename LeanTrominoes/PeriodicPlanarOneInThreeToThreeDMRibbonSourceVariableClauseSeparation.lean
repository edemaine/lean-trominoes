import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableClauseFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRoutingBounds

/-!
# Separating coordinated variable and clause source fans

The mixed finite fan classifier has one exceptional adjacent placement: the
clause center could be the first source neighbor selected by the variable
fan.  A length-at-least-three source route makes that neighbor an internal
route point, so endpoint-only source contact excludes the exception.  This
file combines that fact with source-vertex injectivity and the ordinary
far-macrocell bound.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A source variable prototype never occupies the lifted clause target of
an active occurrence, even when they belong to unrelated incidences. -/
theorem occurrenceSourceVariablePosition_ne_clauseTarget
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase) :
    placement.position first.1.1 ≠
      occurrenceSourceClauseTarget
        presentation.toPlanarIncidencePresentation second := by
  let planar := presentation.toPlanarIncidencePresentation
  let secondData := occurrenceSpliceData planar second
  have firstAtomMember :
      first.1.1 ∈ source.erase.variableOccurrences.dedup := by
    simpa [occurringVariables,
      PeriodicOneInThreeToThreeDM.occurringVariables] using first.atom_mem
  have firstVertexMember :
      CNFVertex.variable first.1.1 ∈
        source.erase.incidenceGraph.vertices := by
    apply List.mem_append.mpr
    left
    exact List.mem_map.mpr ⟨first.1.1, firstAtomMember, rfl⟩
  have secondEdgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase secondData.indexedMember
  have secondEndpointMembers :=
    planar.compatible.1.2 secondData.indexed.1.edge
      (List.fst_mem_of_mem_zipIdx secondEdgeMember)
  have secondClauseVertexMember :
      CNFVertex.clause secondData.indexed.1.clauseIndex ∈
        source.erase.incidenceGraph.vertices := by
    simpa [CNFIncidence.edge, PeriodicCNF.incidenceEdge] using
      secondEndpointMembers.1
  have secondIndexLt :
      secondData.indexed.1.clauseIndex < source.clauses.length :=
    (List.mem_zipIdx' secondData.clauseMember).1
  have secondClauseLookup :
      source.clauses[secondData.indexed.1.clauseIndex] =
        secondData.positionedClause := by
    have lookup :=
      (List.mem_zipIdx_iff_getElem?).mp secondData.clauseMember
    rw [List.getElem?_eq_getElem secondIndexLt] at lookup
    exact Option.some.inj lookup
  let relativeTranslate :=
    Cell.sub
      (PeriodicCNF.clauseAnchor
        secondData.positionedClause.literals)
      secondData.tagged.1.offset
  intro equal
  have liftedEqual :
      PositionedPeriodicCNF.incidenceVertexPositionAt source placement
          (.variable first.1.1) =
        Cell.add (placement.translation relativeTranslate)
          (PositionedPeriodicCNF.incidenceVertexPositionAt source placement
            (.clause secondData.indexed.1.clauseIndex)) := by
    rw [PositionedPeriodicCNF.incidenceVertexPositionAt_clause
      source placement secondData.indexed.1.clauseIndex secondIndexLt,
      secondClauseLookup]
    rw [show
      PositionedPeriodicCNF.incidenceVertexPositionAt source placement
          (.variable first.1.1) =
        placement.position first.1.1 by rfl]
    rw [equal]
    rcases secondData.positionedClause.position with
      ⟨clauseX, clauseY⟩
    rcases PeriodicCNF.clauseAnchor
        secondData.positionedClause.literals with
      ⟨anchorX, anchorY⟩
    rcases secondData.tagged.1.offset with ⟨offsetX, offsetY⟩
    apply Prod.ext <;>
      simp [occurrenceSourceClauseTarget,
        PositionedPeriodicCNF.variableToClauseTarget,
        PositionedPeriodicCNF.canonicalClausePosition,
        PeriodicOneInThreeToThreeDM.reverseOffset,
        PeriodicVariablePlacement.translation,
        relativeTranslate, planar, secondData,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  have verticesEqual :=
    planar.incidenceVertexPositionAt_eq_translated_imp_eq
      firstVertexMember secondClauseVertexMember
      relativeTranslate liftedEqual
  cases verticesEqual

/-- If the first route has a genuine interior point, no lifted source-clause
target can occupy its selected first neighbor. -/
theorem occurrenceSourceClauseTarget_ne_firstVariableNeighbor
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length) :
    occurrenceSourceClauseTarget
        presentation.toPlanarIncidencePresentation second ≠
      Cell.add (placement.position first.1.1)
        (occurrenceSourceVariableDirection
          presentation.toPlanarIncidencePresentation first).step := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstRoute := occurrenceUnitSourceRoute planar first
  let secondRoute := occurrenceUnitSourceRoute planar second
  let secondTarget := occurrenceSourceClauseTarget planar second
  have firstLength' : 3 ≤ firstRoute.length := by
    simpa [firstRoute, planar] using firstLength
  have firstNodup : firstRoute.Nodup := by
    simpa [firstRoute, planar] using
      occurrenceUnitSourceRoute_nodup presentation first
  have firstUnitSteps :
      firstRoute.IsChain AxisDirection.IsUnitAxisStep := by
    simpa [firstRoute] using
      occurrenceUnitSourceRoute_unitSteps planar first
  have firstHead :
      firstRoute.head? = some (placement.position first.1.1) := by
    simpa [firstRoute] using
      occurrenceUnitSourceRoute_variableEndpoint_head? planar first
  have secondTargetMember : secondTarget ∈ secondRoute := by
    simpa [secondTarget, secondRoute,
      occurrenceSourceClauseTarget] using
      occurrenceUnitSourceRoute_clauseEndpoint_mem planar second
  cases firstEquation : firstRoute with
  | nil =>
      simp [firstEquation] at firstLength'
  | cons firstPoint firstTail =>
      cases firstTail with
      | nil =>
          simp [firstEquation] at firstLength'
      | cons firstNext firstRest =>
          cases firstRest with
          | nil =>
              simp [firstEquation] at firstLength'
          | cons firstThird firstRest =>
              have firstPointEq :
                  firstPoint = placement.position first.1.1 := by
                rw [firstEquation] at firstHead
                exact Option.some.inj firstHead
              have firstUnit :
                  AxisDirection.IsUnitAxisStep firstPoint firstNext := by
                rw [firstEquation] at firstUnitSteps
                exact (List.isChain_cons_cons.mp firstUnitSteps).1
              have firstNextEq :
                  firstNext =
                    Cell.add (placement.position first.1.1)
                      (occurrenceSourceVariableDirection
                        planar first).step := by
                change
                  firstNext =
                    Cell.add (placement.position first.1.1)
                      (AxisDirection.polylineFirstDirection firstRoute).step
                rw [firstEquation]
                simp only [AxisDirection.polylineFirstDirection_cons_cons]
                rw [← firstPointEq]
                exact
                  AxisDirection.add_between_step_eq_of_unitAxisStep
                    firstUnit
              have firstNextMember : firstNext ∈ firstRoute := by
                rw [firstEquation]
                simp
              have firstNextInternal :
                  ¬RoutePointIsEndpoint firstRoute firstNext := by
                apply
                  routeCenter_not_endpoint_of_nodup_of_eq_append_triple
                    (leading := []) (trailing := firstRest)
                    (previous := firstPoint) (next := firstThird)
                · simpa [firstEquation]
                · exact firstNodup
              intro targetEq
              have targetEqNext : secondTarget = firstNext := by
                exact targetEq.trans firstNextEq.symm
              by_cases entriesEqual : first = second
              · subst second
                have targetEndpoint :
                    RoutePointIsEndpoint firstRoute secondTarget := by
                  right
                  simpa [firstRoute, secondTarget,
                    occurrenceSourceClauseTarget] using
                    (occurrenceUnitSourceRoute_endpoints planar first).2
                exact firstNextInternal (targetEqNext ▸ targetEndpoint)
              · have differentPoints : firstNext ≠ secondTarget :=
                  routePoints_ne_of_routesMeetOnlyAtEndpoints
                    (occurrenceUnitSourceRoutes_meetOnlyAtEndpoints_of_ne
                      presentation entriesEqual)
                    firstNextMember secondTargetMember
                    (Or.inl firstNextInternal)
                exact differentPoints targetEqNext.symm

/-- A coordinated variable-side fan strictly avoids every coordinated
clause-side fan once its source route has an interior lattice point. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (firstColor secondColor : WireColor)
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation second secondColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstCenter := placement.position first.1.1
  let secondCenter := occurrenceSourceClauseTarget planar second
  rcases ribbonMacrocellCenters_eq_or_far_or_adjacent
      firstCenter secondCenter with
    centersEqual | centersFar | centersAdjacent
  · exact False.elim
      (occurrenceSourceVariablePosition_ne_clauseTarget
        presentation first second centersEqual)
  · exact routesStrictlyAvoidEachOther_of_inFarRibbonMacrocells
      (fun point member =>
        occurrenceCoordinatedRibbonVariableStub_points_bounded
          planar compatible first firstColor member)
      (fun point member =>
        occurrenceCoordinatedRibbonClauseStub_points_bounded
          planar compatible second secondColor member)
      centersFar
  · let firstData := sourceVariableRibbonFanData planar first
    let secondClauseIndex :=
      occurrenceClauseIndex source.erase second.1.1 second.1.2
    let secondData := sourceClauseRibbonFanData planar secondClauseIndex
    let firstSlot := occurrenceVariableSiteSlot first.1.2
    let secondGroup := occurrenceClauseTerminalGroup source.erase second
    let secondLane := routedRibbonLane source.erase second secondColor
    let offset := Cell.sub secondCenter firstCenter
    have firstActive : firstData.SlotActive firstSlot :=
      VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
        planar first
    have secondMember :
        second ∈ activeClauseOccurrenceEntries
          source.erase secondClauseIndex :=
      second.mem_activeClauseOccurrenceEntries
    have secondActive : secondData.GroupActive secondGroup :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        planar secondClauseIndex second secondMember
    have notFirstNeighbor :
        offset ≠ (firstData.direction firstSlot).step := by
      intro offsetEqual
      have targetEqual :
          secondCenter =
            Cell.add firstCenter (firstData.direction firstSlot).step := by
        calc
          secondCenter = Cell.add firstCenter
              (Cell.sub secondCenter firstCenter) := by
            rcases firstCenter with ⟨firstX, firstY⟩
            rcases secondCenter with ⟨secondX, secondY⟩
            simp [Cell.add, Cell.sub]
          _ = Cell.add firstCenter
              (firstData.direction firstSlot).step := by
            rw [← offsetEqual]
      apply
        occurrenceSourceClauseTarget_ne_firstVariableNeighbor
          presentation first second firstLength
      rw [← VariableRibbonFanData.sourceVariableRibbonFanData_direction
        planar first]
      exact targetEqual
    have localAvoid :=
      firstData.coordinatedRoute_strictlyAvoids_clauseCoordinatedRoute_of_adjacent_notFirstNeighbor
        secondData (compatible.1 first) (compatible.2 second)
        firstSlot secondGroup firstActive secondActive
        firstColor secondLane offset centersAdjacent notFirstNeighbor
    have translatedAvoid :=
      localAvoid.translatePolyline (ribbonMacrocellOrigin firstCenter)
    have originEq :
        Cell.add
            (Cell.scale standardThreeStrandLayout.factor offset)
            (ribbonMacrocellOrigin firstCenter) =
          ribbonMacrocellOrigin secondCenter := by
      rcases firstCenter with ⟨firstX, firstY⟩
      rcases secondCenter with ⟨secondX, secondY⟩
      apply Prod.ext <;>
        simp [offset, ribbonMacrocellOrigin,
          Cell.add, Cell.sub, Cell.scale] <;>
        ring
    rw [translatePolyline_add, originEq] at translatedAvoid
    simpa [occurrenceCoordinatedRibbonVariableStub,
      occurrenceCoordinatedRibbonClauseStub,
      planar, firstData, secondData, firstSlot,
      secondClauseIndex, secondGroup, secondLane,
      firstCenter, secondCenter] using translatedAvoid

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
