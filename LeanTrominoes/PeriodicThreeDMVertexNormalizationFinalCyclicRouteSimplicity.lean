import LeanTrominoes.PeriodicThreeDMVertexNormalizationFinalCyclicDrawingSeparation

/-!
# Simplicity of final cyclic-round normalization routes

The generic cyclic boundary lemmas show that each endpoint template meets its
own trimmed corridor only at the advertised splice point.  Together with the
final occurrence-separation theorem, this makes every final route
duplicate-free and geometrically simple.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- For one lifted edge, each cyclic endpoint template shares with its own
corridor exactly the corresponding splice boundary. -/
theorem ContinuousPlanarPresentation.finalNormalizationOccurrence_onlyCommonJunctions
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let sourceRoute := planar.finalNormalizationTemplateOccurrence
      (.source edge) routeTranslate
    let middleRoute := planar.finalNormalizationCorridorOccurrence
      edge routeTranslate
    let targetRoute :=
      (planar.finalNormalizationTemplateOccurrence
        (.target edge) routeTranslate).reverse
    ∃ sourceBoundary targetBoundary,
      (∀ point, point ∈ sourceRoute → point ∈ middleRoute →
        point = sourceBoundary) ∧
      (∀ point, point ∈ middleRoute → point ∈ targetRoute →
        point = targetBoundary) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.normalizationRouteOccurrence2 edge routeTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourcePosition := planar.normalizationEndpointOccurrencePosition2
    sourceEndpoint routeTranslate
  let targetPosition := planar.normalizationEndpointOccurrencePosition2
    targetEndpoint routeTranslate
  let sourcePort := sourceEndpoint.secondNormalizedPort planar
  let targetPort := targetEndpoint.secondNormalizedPort planar
  have routeLength : 2 ≤ oldRoute.length :=
    presentation.normalizationRouteOccurrence2_length_ge_two
      wellFormed degree edgeMember routeTranslate
  have oldSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence2_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    (presentation.normalizationRouteOccurrence2_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  obtain ⟨first, second, rest, sourceEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  obtain ⟨leading, before, last, targetEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have geometry :=
    presentation.normalizationRouteOccurrence2_endpointGeometry
      wellFormed degree edgeMember routeTranslate
  change oldRoute.head? = some sourcePosition ∧
    oldRoute.tail.head? = some
      (Cell.add sourcePosition sourcePort.direction.step) ∧
    oldRoute.getLast? = some targetPosition ∧
    oldRoute.reverse.tail.head? = some
      (Cell.add targetPosition targetPort.direction.step) at geometry
  have firstEqual : first = sourcePosition := by
    rw [sourceEquation] at geometry
    exact Option.some.inj geometry.1
  have secondEqual : second =
      Cell.add sourcePosition sourcePort.direction.step := by
    rw [sourceEquation] at geometry
    exact Option.some.inj geometry.2.1
  have lastEqual : last = targetPosition := by
    rw [targetEquation] at geometry
    apply Option.some.inj
    simpa using geometry.2.2.1
  have beforeEqual : before =
      Cell.add targetPosition targetPort.direction.step := by
    rw [targetEquation] at geometry
    apply Option.some.inj
    simpa using geometry.2.2.2
  subst first
  subst last
  have sourceDirection :
      AxisDirection.between sourcePosition second = sourcePort.direction := by
    rw [secondEqual]
    exact AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine sourcePort)
  have targetDirection :
      AxisDirection.between targetPosition before = targetPort.direction := by
    rw [beforeEqual]
    exact AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine targetPort)
  let sourceBoundary := Cell.add (normalizeVertexPosition sourcePosition)
    (Cell.scale 3 sourcePort.direction.step)
  let targetBoundary := Cell.add (normalizeVertexPosition targetPosition)
    (Cell.scale 3 targetPort.direction.step)
  refine ⟨sourceBoundary, targetBoundary, ?_, ?_⟩
  · intro point templateMember corridorMember
    have common :=
      trimmedMagnifiedRoute_meets_ownRotationRoundTemplate_onlyAt_source
        sourcePosition second rest
        (by simpa [sourceEquation] using oldSimple)
        (by simpa [sourceEquation] using oldOrthogonal)
        sourcePort sourceDirection
        (secondRotationActive planar sourceEndpoint.vertex)
        point
    apply common
    · simpa [PlanarPresentation.finalNormalizationTemplateOccurrence,
        ContractedEndpoint.finalNormalizationTemplate,
        sourcePosition, sourcePort, sourceEndpoint] using templateMember
    · change point ∈ trimmedMagnifiedRoute oldRoute at corridorMember
      rw [sourceEquation] at corridorMember
      exact corridorMember
  · intro point corridorMember templateMember
    have common :=
      trimmedMagnifiedRoute_meets_ownRotationRoundTemplate_onlyAt_target
        leading before targetPosition
        (by simpa [targetEquation] using oldSimple)
        (by simpa [targetEquation] using oldOrthogonal)
        targetPort targetDirection
        (secondRotationActive planar targetEndpoint.vertex)
        point
    apply common
    · have forwardMember : point ∈
          planar.finalNormalizationTemplateOccurrence
            targetEndpoint routeTranslate :=
        List.mem_reverse.mp templateMember
      simpa [PlanarPresentation.finalNormalizationTemplateOccurrence,
        ContractedEndpoint.finalNormalizationTemplate,
        targetPosition, targetPort, targetEndpoint] using forwardMember
    · change point ∈ trimmedMagnifiedRoute oldRoute at corridorMember
      rw [targetEquation] at corridorMember
      exact corridorMember

/-- Every lifted cyclic endpoint template is duplicate-free. -/
theorem PlanarPresentation.finalNormalizationTemplateOccurrence_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (endpointTranslate : Cell) :
    (presentation.finalNormalizationTemplateOccurrence
      endpoint endpointTranslate).Nodup := by
  unfold PlanarPresentation.finalNormalizationTemplateOccurrence
    ContractedEndpoint.finalNormalizationTemplate
  exact normalizationTemplateAt_rotationRoundRoute_nodup _ _ _

/-- Every lifted second-round middle corridor is duplicate-free. -/
theorem ContinuousPlanarPresentation.finalNormalizationCorridorOccurrence_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    (planar.finalNormalizationCorridorOccurrence
      edge routeTranslate).Nodup := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.normalizationRouteOccurrence2 edge routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    (presentation.normalizationRouteOccurrence2_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  have oldSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence2_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have magnifiedNodup : (magnifiedUnitRoute oldRoute).Nodup :=
    magnifiedUnitRoute_nodup oldOrthogonal oldSimple
  unfold PlanarPresentation.finalNormalizationCorridorOccurrence
    trimmedMagnifiedRoute
  have droppedNodup :
      ((magnifiedUnitRoute oldRoute).drop 3).Nodup :=
    List.Pairwise.drop magnifiedNodup
  exact droppedNodup.take

/-- Each complete lifted route produced by the final cyclic splice has no
repeated listed point. -/
theorem ContinuousPlanarPresentation.finalNormalizationRouteOccurrence_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    presentation.toPlanarPresentation
      |>.finalNormalizationRouteOccurrence edge routeTranslate
      |>.Nodup := by
  let planar := presentation.toPlanarPresentation
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourceRoute := planar.finalNormalizationTemplateOccurrence
    sourceEndpoint routeTranslate
  let middleRoute := planar.finalNormalizationCorridorOccurrence
    edge routeTranslate
  let targetForward := planar.finalNormalizationTemplateOccurrence
    targetEndpoint routeTranslate
  let targetRoute := targetForward.reverse
  have sourceNodup : sourceRoute.Nodup :=
    planar.finalNormalizationTemplateOccurrence_nodup
      sourceEndpoint routeTranslate
  have middleNodup : middleRoute.Nodup :=
    presentation.finalNormalizationCorridorOccurrence_nodup
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have targetForwardNodup : targetForward.Nodup :=
    planar.finalNormalizationTemplateOccurrence_nodup
      targetEndpoint routeTranslate
  have targetNodup : targetRoute.Nodup := by
    exact targetForwardNodup.reverse.imp fun different =>
      Ne.symm different
  rcases presentation.finalNormalizationOccurrence_junctions
      wellFormed degree edgeMember routeTranslate with
    ⟨sourceBoundary, targetBoundary,
      sourceLast, middleHead, middleLast, targetHead⟩
  rcases presentation.finalNormalizationOccurrence_onlyCommonJunctions
      wellFormed degree separated sourceSimple edgeMember routeTranslate with
    ⟨sourceCommonBoundary, targetCommonBoundary,
      sourceMiddleOnly, middleTargetOnly⟩
  have sourceCommonBoundaryEq :
      sourceCommonBoundary = sourceBoundary := by
    exact (sourceMiddleOnly sourceBoundary
      (List.mem_of_mem_getLast? sourceLast)
      (List.mem_of_mem_head? middleHead)).symm
  have targetCommonBoundaryEq :
      targetCommonBoundary = targetBoundary := by
    exact (middleTargetOnly targetBoundary
      (List.mem_of_mem_getLast? middleLast)
      (List.mem_of_mem_head? targetHead)).symm
  subst sourceCommonBoundary
  subst targetCommonBoundary
  let oldRoute := planar.normalizationRouteOccurrence2 edge routeTranslate
  have oldRouteSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence2_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have oldGeometry :=
    presentation.normalizationRouteOccurrence2_endpointGeometry
      wellFormed degree edgeMember routeTranslate
  let sourcePosition := planar.normalizationEndpointOccurrencePosition2
    sourceEndpoint routeTranslate
  let targetPosition := planar.normalizationEndpointOccurrencePosition2
    targetEndpoint routeTranslate
  change oldRoute.head? = some sourcePosition ∧ _ ∧
    oldRoute.getLast? = some targetPosition ∧ _ at oldGeometry
  have sourcePositionNeTargetPosition : sourcePosition ≠ targetPosition := by
    intro equal
    have routeLength : 2 ≤ oldRoute.length :=
      presentation.normalizationRouteOccurrence2_length_ge_two
        wellFormed degree edgeMember routeTranslate
    obtain ⟨first, second, rest, routeEquation⟩ :=
      List.exists_eq_cons_cons_of_length_ge_two routeLength
    rw [routeEquation] at oldGeometry oldRouteSimple
    have firstEqual : first = sourcePosition :=
      Option.some.inj oldGeometry.1
    subst first
    have targetInTail : targetPosition ∈ second :: rest := by
      apply List.mem_of_mem_getLast?
      simpa using oldGeometry.2.2.1
    exact (List.nodup_cons.mp oldRouteSimple.1).1
      (equal ▸ targetInTail)
  have sourceTargetStrict : RoutesStrictlyAvoidEachOther
      sourceRoute targetRoute := by
    have forward : RoutesStrictlyAvoidEachOther
        sourceRoute targetForward := by
      unfold sourceRoute targetForward
        PlanarPresentation.finalNormalizationTemplateOccurrence
        ContractedEndpoint.finalNormalizationTemplate
      exact
        normalizationTemplateAt_rotationRoundRoutes_strictlyAvoid_of_positions_ne
          sourcePositionNeTargetPosition
          (secondRotationActive planar sourceEndpoint.vertex)
          (secondRotationActive planar targetEndpoint.vertex)
          (sourceEndpoint.secondNormalizedPort planar)
          (targetEndpoint.secondNormalizedPort planar)
    exact forward.reverse_right
  have middleTargetNodup :
      (joinAtEndpoint middleRoute targetRoute).Nodup :=
    List.Nodup.joinAtEndpoint_of_only_common
      middleNodup targetNodup targetHead middleTargetOnly
  have innerHead :
      (joinAtEndpoint middleRoute targetRoute).head? =
        some sourceBoundary :=
    joinAtEndpoint_head? middleHead
  have sourceInnerOnly :
      ∀ point, point ∈ sourceRoute →
        point ∈ joinAtEndpoint middleRoute targetRoute →
          point = sourceBoundary := by
    intro point sourcePoint innerPoint
    rcases mem_joinAtEndpoint innerPoint with
        middlePoint | targetPoint
    · exact sourceMiddleOnly point sourcePoint middlePoint
    · exact
        (sourceTargetStrict.2.2.2 point sourcePoint
          point targetPoint rfl).elim
  rw [planar.finalNormalizationRouteOccurrence_eq_threePieces]
  exact List.Nodup.joinAtEndpoint_of_only_common
    sourceNodup middleTargetNodup innerHead sourceInnerOnly

/-- Every final normalized contracted route is geometrically simple. -/
theorem ContinuousPlanarPresentation.finalNormalizationRoute_isSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    LocalIncidenceDrawing.RouteIsSimple
      (presentation.toPlanarPresentation.finalNormalizationRoute edge) := by
  let planar := presentation.toPlanarPresentation
  have occurrenceNodup :=
    presentation.finalNormalizationRouteOccurrence_nodup
      wellFormed degree separated sourceSimple edgeMember (0, 0)
  have routeNodup : (planar.finalNormalizationRoute edge).Nodup := by
    change (translatePolyline
      (planar.finalNormalizedGridDrawing.periodTranslation (0, 0))
      (planar.finalNormalizationRoute edge)).Nodup at occurrenceNodup
    rw [show planar.finalNormalizedGridDrawing.periodTranslation (0, 0) =
        (0, 0) by
      simp [PeriodicGridDrawing.periodTranslation, Cell.scale],
      PeriodicOrthocrossing.translatePolyline_zero] at occurrenceNodup
    exact occurrenceNodup
  exact routeIsSimple_of_unitSteps_of_nodup
    (presentation.finalNormalizationRoute_unitSteps
      wellFormed degree edgeMember)
    routeNodup

/-- All routes stored in the final normalized drawing are
geometrically simple. -/
theorem ContinuousPlanarPresentation.finalNormalizedGridDrawing_routesSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈
        presentation.toPlanarPresentation.finalNormalizedGridDrawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  let planar := presentation.toPlanarPresentation
  intro route routeMember
  rcases List.mem_iff_get.mp routeMember with ⟨index, routeAt⟩
  have taggedMember :
      (route, index.val) ∈
        planar.finalNormalizedGridDrawing.edgeRoutes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨index.isLt, routeAt⟩
  rcases planar.finalNormalizedGridDrawing_route_has_edge taggedMember with
    ⟨edge, edgeMember, routeEq⟩
  change route = planar.finalNormalizationRoute edge at routeEq
  rw [routeEq]
  exact presentation.finalNormalizationRoute_isSimple
    wellFormed degree separated sourceSimple
      (List.fst_mem_of_mem_zipIdx edgeMember)

/-- Consequently the final normalized drawing has the
endpoint-only listed-point contact certificate needed by rasterization. -/
theorem ContinuousPlanarPresentation.finalNormalizedGridDrawing_routePointsMeetOnlyAtEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.finalNormalizedGridDrawing
      |>.RoutePointsMeetOnlyAtEndpoints :=
  PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
    (presentation.finalNormalizedGridDrawing_liftedRoutesAvoidEachOther
      wellFormed degree separated sourceSimple)
    (presentation.finalNormalizedGridDrawing_routesSimple
      wellFormed degree separated sourceSimple)

end PeriodicThreeDM
end LeanTrominoes
