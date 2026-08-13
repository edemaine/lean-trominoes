/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationCyclicDrawingSeparation

/-!
# Simplicity of first cyclic-round normalization routes

For unit lattice routes, geometric simplicity follows from a duplicate-free
point list.  Each cyclic endpoint template and trimmed corridor is separately
duplicate-free; a directional boundary argument shows that an endpoint
template meets its own corridor only at their advertised splice point.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- A selected cyclic route stays no farther outward than its boundary point
in its incoming old-port direction. -/
theorem rotationRoundRoute_linearValue_le_boundary
    (active : Bool) (oldPort : CanonicalVertexPort) :
    ∀ point ∈ (rotationRoundPortAndRoute active oldPort).2,
      Cell.linearValue oldPort.direction.step point ≤
        Cell.linearValue oldPort.direction.step center + 3 := by
  cases active <;> cases oldPort <;>
    simp_all [rotationRoundPortAndRoute, newPortAfterClockwise,
      identityRotationRoute, clockwiseRotationRoute,
      CanonicalVertexPort.direction, AxisDirection.step,
      Cell.linearValue, center]

/-- The cyclic route's three-step boundary is its unique point on the outer
supporting line perpendicular to the incoming old port. -/
theorem rotationRoundRoute_eq_boundary_of_linearValue_eq
    (active : Bool) (oldPort : CanonicalVertexPort) :
    ∀ point ∈ (rotationRoundPortAndRoute active oldPort).2,
      Cell.linearValue oldPort.direction.step point =
          Cell.linearValue oldPort.direction.step center + 3 →
        point = Cell.add center (Cell.scale 3 oldPort.direction.step) := by
  cases active <;> cases oldPort <;>
    simp_all [rotationRoundPortAndRoute, newPortAfterClockwise,
      identityRotationRoute, clockwiseRotationRoute,
      CanonicalVertexPort.direction, AxisDirection.step,
      Cell.linearValue, center, Cell.add, Cell.scale]

/-- Anchoring preserves the cyclic route's outer half-plane bound. -/
theorem normalizationTemplateAt_rotationRoundRoute_linearValue_le_boundary
    (position : Cell) (active : Bool)
    (oldPort : CanonicalVertexPort) :
    ∀ point ∈ normalizationTemplateAt position
        (rotationRoundPortAndRoute active oldPort).2,
      Cell.linearValue oldPort.direction.step point ≤
        Cell.linearValue oldPort.direction.step
          (normalizeVertexPosition position) + 3 := by
  intro point pointMember
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  have localBound := rotationRoundRoute_linearValue_le_boundary
    active oldPort localPoint localMember
  simp only [normalizeVertexPosition, Cell.linearValue_add]
  omega

/-- The anchored cyclic route's only outer-supporting-line point is its
three-step splice boundary. -/
theorem normalizationTemplateAt_rotationRoundRoute_eq_boundary_of_linearValue_eq
    (position : Cell) (active : Bool)
    (oldPort : CanonicalVertexPort) :
    ∀ point ∈ normalizationTemplateAt position
        (rotationRoundPortAndRoute active oldPort).2,
      Cell.linearValue oldPort.direction.step point =
          Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition position) + 3 →
        point = Cell.add (normalizeVertexPosition position)
          (Cell.scale 3 oldPort.direction.step) := by
  intro point pointMember equal
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, pointEq⟩
  subst point
  have localEqual :
      Cell.linearValue oldPort.direction.step localPoint =
        Cell.linearValue oldPort.direction.step center + 3 := by
    simp only [normalizeVertexPosition, Cell.linearValue_add] at equal
    omega
  have boundary :=
    rotationRoundRoute_eq_boundary_of_linearValue_eq
      active oldPort localPoint localMember localEqual
  subst localPoint
  rcases position with ⟨positionX, positionY⟩
  cases oldPort <;>
    simp [normalizeVertexPosition, center, vertexNormalizationScale,
      CanonicalVertexPort.direction, AxisDirection.step,
      Cell.add, Cell.scale] <;> ring

/-- At the source of a simple old route, its cyclic endpoint template and
trimmed magnified corridor share only their splice boundary. -/
theorem trimmedMagnifiedRoute_meets_ownRotationRoundTemplate_onlyAt_source
    (first second : Cell) (rest : List Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (first :: second :: rest))
    (orthogonal : OrthogonalPolyline (first :: second :: rest))
    (oldPort : CanonicalVertexPort)
    (direction : AxisDirection.between first second = oldPort.direction)
    (active : Bool) :
    ∀ point,
      point ∈ normalizationTemplateAt first
          (rotationRoundPortAndRoute active oldPort).2 →
      point ∈ trimmedMagnifiedRoute (first :: second :: rest) →
      point = Cell.add (normalizeVertexPosition first)
        (Cell.scale 3 oldPort.direction.step) := by
  let template := normalizationTemplateAt first
    (rotationRoundPortAndRoute active oldPort).2
  let radial :=
    (AxisDirection.unitSegmentPoints
      (normalizeVertexPosition first)
      (normalizeVertexPosition second)).drop 3
  have aligned : (GridSegment.mk first second).IsAxisAligned :=
    (List.isChain_cons_cons.mp orthogonal).1
  have radialBound :
      ∀ point ∈ radial,
        Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition first) + 2 <
          Cell.linearValue oldPort.direction.step point := by
    have directionSide :
        AxisDirection.between first second =
          oldPort.vertexSide.direction := by
      simpa using direction
    simpa using
      (unitSegmentPoints_drop_three_linearValue_gt oldPort.vertexSide
        ((between_normalizeVertexPosition first second).trans directionSide))
  have templateBound :
      ∀ point ∈ template,
        Cell.linearValue oldPort.direction.step point ≤
          Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition first) + 3 :=
    normalizationTemplateAt_rotationRoundRoute_linearValue_le_boundary
      first active oldPort
  have tailAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.tail_avoids_head
      (head := first) simple (by simp)
  have tailStrict :
      RoutesStrictlyAvoidEachOther
        (magnifiedUnitRoute (second :: rest)) template :=
    magnifiedUnitRoute_strictlyAvoids_rotationRoundTemplate
      (List.isChain_cons_cons.mp orthogonal).2
      (by simpa using tailAvoids.1)
      (by
        intro segment segmentMember segmentAligned
        exact tailAvoids.2 segment
          (by simpa using segmentMember) segmentAligned)
      active oldPort
  intro point templateMember corridorMember
  have droppedMember :
      point ∈
        (magnifiedUnitRoute (first :: second :: rest)).drop 3 :=
    List.mem_of_mem_take corridorMember
  rw [magnifiedUnitRoute_drop_three_cons_cons
    first second rest aligned] at droppedMember
  rcases mem_joinAtEndpoint droppedMember with
      radialMember | tailMember
  · have lower := radialBound point radialMember
    have upper := templateBound point templateMember
    apply
      normalizationTemplateAt_rotationRoundRoute_eq_boundary_of_linearValue_eq
        first active oldPort point templateMember
    omega
  · exact
      (tailStrict.2.2.2 point tailMember
        point templateMember rfl).elim

/-- Symmetric target-end version of the own cyclic-template boundary
classification. -/
theorem trimmedMagnifiedRoute_meets_ownRotationRoundTemplate_onlyAt_target
    (leading : List Cell) (before last : Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (leading ++ [before, last]))
    (orthogonal : OrthogonalPolyline (leading ++ [before, last]))
    (oldPort : CanonicalVertexPort)
    (direction : AxisDirection.between last before = oldPort.direction)
    (active : Bool) :
    ∀ point,
      point ∈ normalizationTemplateAt last
          (rotationRoundPortAndRoute active oldPort).2 →
      point ∈ trimmedMagnifiedRoute (leading ++ [before, last]) →
      point = Cell.add (normalizeVertexPosition last)
        (Cell.scale 3 oldPort.direction.step) := by
  let oldPrefix := leading ++ [before]
  let initialRoute := magnifiedUnitRoute oldPrefix
  let finalSegment := AxisDirection.unitSegmentPoints
    (normalizeVertexPosition before) (normalizeVertexPosition last)
  let radial := finalSegment.reverse.drop 3
  let template := normalizationTemplateAt last
    (rotationRoundPortAndRoute active oldPort).2
  have aligned : (GridSegment.mk before last).IsAxisAligned :=
    (List.isChain_append_cons_cons.mp orthogonal).2.1
  have prefixOrthogonal : OrthogonalPolyline oldPrefix :=
    (List.isChain_append_cons_cons.mp orthogonal).1
  have normalizedAligned :
      (GridSegment.mk
        (normalizeVertexPosition before)
        (normalizeVertexPosition last)).IsAxisAligned := by
    have scaledAligned :
        (GridSegment.scale vertexNormalizationScale
          (GridSegment.mk before last)).IsAxisAligned :=
      (GridSegment.isAxisAligned_scale_iff
        (by norm_num [vertexNormalizationScale])
        (GridSegment.mk before last)).2 aligned
    have translatedAligned :=
      (GridSegment.isAxisAligned_translate
        (GridSegment.scale vertexNormalizationScale
          (GridSegment.mk before last)) center).2 scaledAligned
    simpa [GridSegment.scale, GridSegment.translate,
      normalizeVertexPosition, Cell.add_comm] using translatedAligned
  have radialBound :
      ∀ point ∈ radial,
        Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition last) + 2 <
          Cell.linearValue oldPort.direction.step point := by
    have directionSide :
        AxisDirection.between last before =
          oldPort.vertexSide.direction := by
      simpa using direction
    simpa using
      (unitSegmentPoints_reverse_drop_three_linearValue_gt
        oldPort.vertexSide normalizedAligned
          ((between_normalizeVertexPosition last before).trans
            directionSide))
  have templateBound :
      ∀ point ∈ template,
        Cell.linearValue oldPort.direction.step point ≤
          Cell.linearValue oldPort.direction.step
            (normalizeVertexPosition last) + 3 :=
    normalizationTemplateAt_rotationRoundRoute_linearValue_le_boundary
      last active oldPort
  have prefixAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.dropLast_avoids_last
      (last := last) simple (by simp)
  have initialStrict :
      RoutesStrictlyAvoidEachOther initialRoute template :=
    magnifiedUnitRoute_strictlyAvoids_rotationRoundTemplate
      prefixOrthogonal
      (by simpa [oldPrefix] using prefixAvoids.1)
      (by
        intro segment segmentMember segmentAligned
        exact prefixAvoids.2 segment
          (by simpa [oldPrefix] using segmentMember) segmentAligned)
      active oldPort
  have prefixLast : oldPrefix.getLast? = some before := by
    simp [oldPrefix]
  have initialLast :
      initialRoute.getLast? = some (normalizeVertexPosition before) := by
    have preserved := magnifiedUnitRoute_getLast?
      (points := oldPrefix) (by simp [oldPrefix]) prefixOrthogonal
    simpa [initialRoute, oldPrefix, prefixLast] using preserved
  have finalHead :
      finalSegment.head? = some (normalizeVertexPosition before) :=
    AxisDirection.unitSegmentPoints_head? _ _
  have finalLong : 3 < finalSegment.length := by
    simp only [finalSegment, AxisDirection.unitSegmentPoints_length,
      segmentLength_normalizeVertexPosition]
    have positive :=
      AxisDirection.segmentLength_positive_of_axisAligned aligned
    omega
  have magnifiedEquation :
      magnifiedUnitRoute (leading ++ [before, last]) =
        joinAtEndpoint initialRoute finalSegment := by
    unfold magnifiedUnitRoute
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [unitSubdividePolyline_append_pair]
    simp [initialRoute, oldPrefix, finalSegment, magnifiedUnitRoute]
  have reversedMagnifiedEquation :
      (magnifiedUnitRoute (leading ++ [before, last])).reverse =
        joinAtEndpoint finalSegment.reverse initialRoute.reverse := by
    rw [magnifiedEquation]
    exact joinAtEndpoint_reverse initialLast finalHead
  have droppedReversedEquation :
      (magnifiedUnitRoute
        (leading ++ [before, last])).reverse.drop 3 =
        joinAtEndpoint radial initialRoute.reverse := by
    rw [reversedMagnifiedEquation]
    unfold radial joinAtEndpoint
    rw [List.drop_append_of_le_length]
    simpa [List.length_reverse] using le_of_lt finalLong
  have reversedTrimEquation :
      (trimmedMagnifiedRoute
        (leading ++ [before, last])).reverse =
        ((magnifiedUnitRoute
          (leading ++ [before, last])).reverse.drop 3).take
            ((magnifiedUnitRoute
              (leading ++ [before, last])).length - 6) := by
    unfold trimmedMagnifiedRoute
    exact (List.symmetricTrim_reverse
      (magnifiedUnitRoute (leading ++ [before, last]))).symm
  intro point templateMember corridorMember
  have reversedMember :
      point ∈ (trimmedMagnifiedRoute
        (leading ++ [before, last])).reverse :=
    List.mem_reverse.mpr corridorMember
  rw [reversedTrimEquation] at reversedMember
  have droppedMember := List.mem_of_mem_take reversedMember
  rw [droppedReversedEquation] at droppedMember
  rcases mem_joinAtEndpoint droppedMember with
      radialMember | initialReverseMember
  · have lower := radialBound point radialMember
    have upper := templateBound point templateMember
    apply
      normalizationTemplateAt_rotationRoundRoute_eq_boundary_of_linearValue_eq
        last active oldPort point templateMember
    omega
  · have initialMember : point ∈ initialRoute :=
      List.mem_reverse.mp initialReverseMember
    exact
      (initialStrict.2.2.2 point initialMember
        point templateMember rfl).elim

/-- For one lifted edge, each cyclic endpoint template shares with its own
corridor exactly the corresponding splice boundary. -/
theorem ContinuousPlanarPresentation.secondNormalizationOccurrence_onlyCommonJunctions
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
    let sourceRoute := planar.secondNormalizationTemplateOccurrence
      (.source edge) routeTranslate
    let middleRoute := planar.secondNormalizationCorridorOccurrence
      edge routeTranslate
    let targetRoute :=
      (planar.secondNormalizationTemplateOccurrence
        (.target edge) routeTranslate).reverse
    ∃ sourceBoundary targetBoundary,
      (∀ point, point ∈ sourceRoute → point ∈ middleRoute →
        point = sourceBoundary) ∧
      (∀ point, point ∈ middleRoute → point ∈ targetRoute →
        point = targetBoundary) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.normalizationRouteOccurrence1 edge routeTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourcePosition := planar.normalizationEndpointOccurrencePosition1
    sourceEndpoint routeTranslate
  let targetPosition := planar.normalizationEndpointOccurrencePosition1
    targetEndpoint routeTranslate
  let sourcePort := sourceEndpoint.firstNormalizedPort planar
  let targetPort := targetEndpoint.firstNormalizedPort planar
  have routeLength : 2 ≤ oldRoute.length :=
    presentation.normalizationRouteOccurrence1_length_ge_two
      degree edgeMember routeTranslate
  have oldSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence1_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    (presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  obtain ⟨first, second, rest, sourceEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  obtain ⟨leading, before, last, targetEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have geometry :=
    presentation.normalizationRouteOccurrence1_endpointGeometry
      degree edgeMember routeTranslate
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
        (firstRotationActive planar sourceEndpoint.vertex)
        point
    apply common
    · simpa [PlanarPresentation.secondNormalizationTemplateOccurrence,
        ContractedEndpoint.secondNormalizationTemplate,
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
        (firstRotationActive planar targetEndpoint.vertex)
        point
    apply common
    · have forwardMember : point ∈
          planar.secondNormalizationTemplateOccurrence
            targetEndpoint routeTranslate :=
        List.mem_reverse.mp templateMember
      simpa [PlanarPresentation.secondNormalizationTemplateOccurrence,
        ContractedEndpoint.secondNormalizationTemplate,
        targetPosition, targetPort, targetEndpoint] using forwardMember
    · change point ∈ trimmedMagnifiedRoute oldRoute at corridorMember
      rw [targetEquation] at corridorMember
      exact corridorMember

/-- Every lifted cyclic endpoint template is duplicate-free. -/
theorem PlanarPresentation.secondNormalizationTemplateOccurrence_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (endpointTranslate : Cell) :
    (presentation.secondNormalizationTemplateOccurrence
      endpoint endpointTranslate).Nodup := by
  unfold PlanarPresentation.secondNormalizationTemplateOccurrence
    ContractedEndpoint.secondNormalizationTemplate
  exact normalizationTemplateAt_rotationRoundRoute_nodup _ _ _

/-- Every lifted second-round middle corridor is duplicate-free. -/
theorem ContinuousPlanarPresentation.secondNormalizationCorridorOccurrence_nodup
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
    (planar.secondNormalizationCorridorOccurrence
      edge routeTranslate).Nodup := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.normalizationRouteOccurrence1 edge routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    (presentation.normalizationRouteOccurrence1_unitSteps
      wellFormed degree edgeMember routeTranslate).imp
        (fun _ _ step => step.isAxisAligned)
  have oldSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence1_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have magnifiedNodup : (magnifiedUnitRoute oldRoute).Nodup :=
    magnifiedUnitRoute_nodup oldOrthogonal oldSimple
  unfold PlanarPresentation.secondNormalizationCorridorOccurrence
    trimmedMagnifiedRoute
  have droppedNodup :
      ((magnifiedUnitRoute oldRoute).drop 3).Nodup :=
    List.Pairwise.drop magnifiedNodup
  exact droppedNodup.take

/-- Each complete lifted route produced by the first cyclic splice has no
repeated listed point. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrence2_nodup
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
      |>.normalizationRouteOccurrence2 edge routeTranslate
      |>.Nodup := by
  let planar := presentation.toPlanarPresentation
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourceRoute := planar.secondNormalizationTemplateOccurrence
    sourceEndpoint routeTranslate
  let middleRoute := planar.secondNormalizationCorridorOccurrence
    edge routeTranslate
  let targetForward := planar.secondNormalizationTemplateOccurrence
    targetEndpoint routeTranslate
  let targetRoute := targetForward.reverse
  have sourceNodup : sourceRoute.Nodup :=
    planar.secondNormalizationTemplateOccurrence_nodup
      sourceEndpoint routeTranslate
  have middleNodup : middleRoute.Nodup :=
    presentation.secondNormalizationCorridorOccurrence_nodup
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have targetForwardNodup : targetForward.Nodup :=
    planar.secondNormalizationTemplateOccurrence_nodup
      targetEndpoint routeTranslate
  have targetNodup : targetRoute.Nodup := by
    exact targetForwardNodup.reverse.imp fun different =>
      Ne.symm different
  rcases presentation.secondNormalizationOccurrence_junctions
      wellFormed degree edgeMember routeTranslate with
    ⟨sourceBoundary, targetBoundary,
      sourceLast, middleHead, middleLast, targetHead⟩
  rcases presentation.secondNormalizationOccurrence_onlyCommonJunctions
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
  let oldRoute := planar.normalizationRouteOccurrence1 edge routeTranslate
  have oldRouteSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.normalizationRouteOccurrence1_isSimple
      wellFormed degree separated sourceSimple edgeMember routeTranslate
  have oldGeometry :=
    presentation.normalizationRouteOccurrence1_endpointGeometry
      degree edgeMember routeTranslate
  let sourcePosition := planar.normalizationEndpointOccurrencePosition1
    sourceEndpoint routeTranslate
  let targetPosition := planar.normalizationEndpointOccurrencePosition1
    targetEndpoint routeTranslate
  change oldRoute.head? = some sourcePosition ∧ _ ∧
    oldRoute.getLast? = some targetPosition ∧ _ at oldGeometry
  have sourcePositionNeTargetPosition : sourcePosition ≠ targetPosition := by
    intro equal
    have routeLength : 2 ≤ oldRoute.length :=
      presentation.normalizationRouteOccurrence1_length_ge_two
        degree edgeMember routeTranslate
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
        PlanarPresentation.secondNormalizationTemplateOccurrence
        ContractedEndpoint.secondNormalizationTemplate
      exact
        normalizationTemplateAt_rotationRoundRoutes_strictlyAvoid_of_positions_ne
          sourcePositionNeTargetPosition
          (firstRotationActive planar sourceEndpoint.vertex)
          (firstRotationActive planar targetEndpoint.vertex)
          (sourceEndpoint.firstNormalizedPort planar)
          (targetEndpoint.firstNormalizedPort planar)
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
  rw [planar.normalizationRouteOccurrence2_eq_threePieces]
  exact List.Nodup.joinAtEndpoint_of_only_common
    sourceNodup middleTargetNodup innerHead sourceInnerOnly

/-- Every second-round normalized contracted route is geometrically simple. -/
theorem ContinuousPlanarPresentation.normalizationRoute2_isSimple
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
      (presentation.toPlanarPresentation.normalizationRoute2 edge) := by
  let planar := presentation.toPlanarPresentation
  have occurrenceNodup :=
    presentation.normalizationRouteOccurrence2_nodup
      wellFormed degree separated sourceSimple edgeMember (0, 0)
  have routeNodup : (planar.normalizationRoute2 edge).Nodup := by
    change (translatePolyline
      (planar.normalizationGridDrawing2.periodTranslation (0, 0))
      (planar.normalizationRoute2 edge)).Nodup at occurrenceNodup
    rw [show planar.normalizationGridDrawing2.periodTranslation (0, 0) =
        (0, 0) by
      simp [PeriodicGridDrawing.periodTranslation, Cell.scale],
      PeriodicOrthocrossing.translatePolyline_zero] at occurrenceNodup
    exact occurrenceNodup
  exact routeIsSimple_of_unitSteps_of_nodup
    (presentation.normalizationRoute2_unitSteps
      wellFormed degree edgeMember)
    routeNodup

/-- All routes stored in the second intermediate normalization drawing are
geometrically simple. -/
theorem ContinuousPlanarPresentation.normalizationGridDrawing2_routesSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈
        presentation.toPlanarPresentation.normalizationGridDrawing2.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  let planar := presentation.toPlanarPresentation
  intro route routeMember
  rcases List.mem_iff_get.mp routeMember with ⟨index, routeAt⟩
  have taggedMember :
      (route, index.val) ∈
        planar.normalizationGridDrawing2.edgeRoutes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨index.isLt, routeAt⟩
  rcases planar.normalizationGridDrawing2_route_has_edge taggedMember with
    ⟨edge, edgeMember, routeEq⟩
  change route = planar.normalizationRoute2 edge at routeEq
  rw [routeEq]
  exact presentation.normalizationRoute2_isSimple
    wellFormed degree separated sourceSimple
      (List.fst_mem_of_mem_zipIdx edgeMember)

/-- Consequently the second intermediate normalization drawing has the
endpoint-only listed-point contact certificate needed by the final round. -/
theorem ContinuousPlanarPresentation.normalizationGridDrawing2_routePointsMeetOnlyAtEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.normalizationGridDrawing2
      |>.RoutePointsMeetOnlyAtEndpoints :=
  PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
    (presentation.normalizationGridDrawing2_liftedRoutesAvoidEachOther
      wellFormed degree separated sourceSimple)
    (presentation.normalizationGridDrawing2_routesSimple
      wellFormed degree separated sourceSimple)

end PeriodicThreeDM
end LeanTrominoes
