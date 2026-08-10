import LeanTrominoes.PeriodicThreeDMVertexNormalizationDrawingSeparation
import LeanTrominoes.OrthogonalPolylineLoopErasure

/-!
# Simplicity of first-round normalization routes

The first local splice preserves simplicity of each individual stored route.
For unit lattice routes, it is enough to prove that the point list has no
duplicates.  The duplicate-free proof separates the source and target
templates from the trimmed middle corridor, retaining exactly the two splice
boundary points.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

/-- A duplicate-free chain of unit lattice steps is geometrically simple. -/
theorem routeIsSimple_of_unitSteps_of_nodup
    {route : List Cell}
    (unitSteps : route.IsChain AxisDirection.IsUnitAxisStep)
    (nodup : route.Nodup) :
    LocalIncidenceDrawing.RouteIsSimple route := by
  cases route with
  | nil => simp [LocalIncidenceDrawing.RouteIsSimple,
      gridPolylineSegments]
  | cons first rest =>
      let walk := SimpleGraph.Walk.ofSupport
        (first :: rest) (by simp)
        (unitSteps.imp fun source target step =>
          (AxisDirection.unitAxisGraph_adj_iff source target).mpr step)
      have support : walk.support = first :: rest := by
        dsimp only [walk]
        apply SimpleGraph.Walk.support_ofSupport
      have path : walk.IsPath := by
        rw [SimpleGraph.Walk.isPath_def, support]
        exact nodup
      rw [← support]
      exact AxisDirection.routeIsSimple_support_of_unitAxisPath path

/-- An endpoint join is duplicate-free when its pieces are duplicate-free
and their advertised boundary is their only common listed point. -/
theorem List.Nodup.joinAtEndpoint_of_only_common
    {first second : List Cell} {boundary : Cell}
    (firstNodup : first.Nodup)
    (secondNodup : second.Nodup)
    (secondHead : second.head? = some boundary)
    (onlyCommon :
      ∀ point, point ∈ first → point ∈ second →
        point = boundary) :
    (joinAtEndpoint first second).Nodup := by
  have disjoint : List.Disjoint first second.tail := by
    rw [List.disjoint_left]
    intro point firstMember secondTailMember
    have pointEq := onlyCommon point firstMember
      (List.mem_of_mem_tail secondTailMember)
    cases second with
    | nil => simp at secondHead
    | cons actualBoundary rest =>
        have boundaryEq : actualBoundary = boundary := by
          simpa using secondHead
        subst actualBoundary
        have boundaryFresh : boundary ∉ rest :=
          (List.nodup_cons.mp secondNodup).1
        exact boundaryFresh (by simpa [pointEq] using secondTailMember)
  unfold joinAtEndpoint
  exact firstNodup.append secondNodup.tail disjoint

namespace DegreeThreeVertexNormalization

/-- Every finite Figure 2 arm has no repeated listed point. -/
theorem route_nodup (omitted : VertexSide)
    (port : CanonicalVertexPort) :
    (route omitted port).Nodup := by
  cases omitted <;> cases port <;> native_decide

/-- The selected Figure 2 arm lies no farther outward than its boundary
midpoint in the old side assigned to that arm. -/
theorem route_linearValue_le_boundary
    (omitted side : VertexSide)
    (used : side ≠ omitted) :
    ∀ point ∈ route omitted (canonicalPortForSide omitted side),
      Cell.linearValue side.direction.step point ≤
        Cell.linearValue side.direction.step center + 3 := by
  cases omitted <;> cases side <;>
    simp_all [route, canonicalPortForSide, VertexSide.direction,
      AxisDirection.step, Cell.linearValue, center]

/-- The boundary midpoint is the selected Figure 2 arm's unique point on
its outer supporting line. -/
theorem route_eq_boundaryPoint_of_linearValue_eq
    (omitted side : VertexSide)
    (used : side ≠ omitted) :
    ∀ point ∈ route omitted (canonicalPortForSide omitted side),
      Cell.linearValue side.direction.step point =
          Cell.linearValue side.direction.step center + 3 →
        point = boundaryPoint side := by
  cases omitted <;> cases side <;>
    simp_all [route, canonicalPortForSide, VertexSide.direction,
      AxisDirection.step, Cell.linearValue, center, boundaryPoint]

end DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Anchoring a Figure 2 arm preserves its duplicate-free point list. -/
theorem normalizationTemplateAt_route_nodup
    (position : Cell) (omitted : VertexSide)
    (port : CanonicalVertexPort) :
    (normalizationTemplateAt position (route omitted port)).Nodup := by
  unfold normalizationTemplateAt translatePolyline
  exact (DegreeThreeVertexNormalization.route_nodup omitted port).map
    (Cell.add_left_injective (Cell.scale vertexNormalizationScale position))

/-- The selected anchored arm stays on the center side of its old boundary
supporting line. -/
theorem normalizationTemplateAt_route_linearValue_le_boundary
    (position : Cell) (omitted side : VertexSide)
    (used : side ≠ omitted) :
    ∀ point ∈
        normalizationTemplateAt position
          (route omitted (canonicalPortForSide omitted side)),
      Cell.linearValue side.direction.step point ≤
        Cell.linearValue side.direction.step
          (normalizeVertexPosition position) + 3 := by
  intro point pointMember
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  have localBound :=
    DegreeThreeVertexNormalization.route_linearValue_le_boundary
      omitted side used localPoint localMember
  simp only [normalizeVertexPosition, Cell.linearValue_add]
  omega

/-- The selected anchored arm's only point on its outer supporting line is
the three-step splice boundary. -/
theorem normalizationTemplateAt_route_eq_boundary_of_linearValue_eq
    (position : Cell) (omitted side : VertexSide)
    (used : side ≠ omitted) :
    ∀ point ∈
        normalizationTemplateAt position
          (route omitted (canonicalPortForSide omitted side)),
      Cell.linearValue side.direction.step point =
          Cell.linearValue side.direction.step
            (normalizeVertexPosition position) + 3 →
        point = Cell.add (normalizeVertexPosition position)
          (Cell.scale 3 side.direction.step) := by
  intro point pointMember equal
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, pointEq⟩
  subst point
  have localEqual :
      Cell.linearValue side.direction.step localPoint =
        Cell.linearValue side.direction.step center + 3 := by
    simp only [normalizeVertexPosition, Cell.linearValue_add] at equal
    omega
  have boundary :=
    DegreeThreeVertexNormalization.route_eq_boundaryPoint_of_linearValue_eq
      omitted side used localPoint localMember localEqual
  subst localPoint
  rcases position with ⟨positionX, positionY⟩
  cases side <;>
    simp [normalizeVertexPosition, boundaryPoint, center,
      vertexNormalizationScale,
      VertexSide.direction, AxisDirection.step, Cell.add, Cell.scale] <;>
      ring

/-- At the source of a simple old route, the selected Figure 2 arm and the
trimmed magnified corridor share only their splice boundary. -/
theorem trimmedMagnifiedRoute_meets_ownTemplate_onlyAt_source
    (first second : Cell) (rest : List Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (first :: second :: rest))
    (orthogonal : OrthogonalPolyline (first :: second :: rest))
    (side : VertexSide)
    (direction : AxisDirection.between first second = side.direction)
    (omitted : VertexSide) (used : side ≠ omitted) :
    ∀ point,
      point ∈ normalizationTemplateAt first
          (route omitted (canonicalPortForSide omitted side)) →
      point ∈ trimmedMagnifiedRoute (first :: second :: rest) →
      point = Cell.add (normalizeVertexPosition first)
        (Cell.scale 3 side.direction.step) := by
  let template := normalizationTemplateAt first
    (route omitted (canonicalPortForSide omitted side))
  let radial :=
    (AxisDirection.unitSegmentPoints
      (normalizeVertexPosition first)
      (normalizeVertexPosition second)).drop 3
  have aligned : (GridSegment.mk first second).IsAxisAligned :=
    (List.isChain_cons_cons.mp orthogonal).1
  have radialBound :
      ∀ point ∈ radial,
        Cell.linearValue side.direction.step
            (normalizeVertexPosition first) + 2 <
          Cell.linearValue side.direction.step point := by
    exact unitSegmentPoints_drop_three_linearValue_gt side
      ((between_normalizeVertexPosition first second).trans direction)
  have templateBound :
      ∀ point ∈ template,
        Cell.linearValue side.direction.step point ≤
          Cell.linearValue side.direction.step
            (normalizeVertexPosition first) + 3 := by
    exact normalizationTemplateAt_route_linearValue_le_boundary
      first omitted side used
  have tailAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.tail_avoids_head
      (head := first) simple (by simp)
  have tailStrict :
      RoutesStrictlyAvoidEachOther
        (magnifiedUnitRoute (second :: rest)) template := by
    exact magnifiedUnitRoute_strictlyAvoids_normalizationTemplateAt_route
      (List.isChain_cons_cons.mp orthogonal).2
      (by simpa using tailAvoids.1)
      (by
        intro segment segmentMember segmentAligned
        exact tailAvoids.2 segment
          (by simpa using segmentMember) segmentAligned)
      omitted (canonicalPortForSide omitted side)
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
    apply normalizationTemplateAt_route_eq_boundary_of_linearValue_eq
      first omitted side used point templateMember
    omega
  · exact
      (tailStrict.2.2.2 point tailMember
        point templateMember rfl).elim

/-- The symmetric target-end statement: the selected Figure 2 arm and the
trimmed corridor share only their target splice boundary. -/
theorem trimmedMagnifiedRoute_meets_ownTemplate_onlyAt_target
    (leading : List Cell) (before last : Cell)
    (simple : LocalIncidenceDrawing.RouteIsSimple
      (leading ++ [before, last]))
    (orthogonal : OrthogonalPolyline (leading ++ [before, last]))
    (side : VertexSide)
    (direction : AxisDirection.between last before = side.direction)
    (omitted : VertexSide) (used : side ≠ omitted) :
    ∀ point,
      point ∈ normalizationTemplateAt last
          (route omitted (canonicalPortForSide omitted side)) →
      point ∈ trimmedMagnifiedRoute (leading ++ [before, last]) →
      point = Cell.add (normalizeVertexPosition last)
        (Cell.scale 3 side.direction.step) := by
  let oldPrefix := leading ++ [before]
  let initialRoute := magnifiedUnitRoute oldPrefix
  let finalSegment := AxisDirection.unitSegmentPoints
    (normalizeVertexPosition before) (normalizeVertexPosition last)
  let radial := finalSegment.reverse.drop 3
  let template := normalizationTemplateAt last
    (route omitted (canonicalPortForSide omitted side))
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
        Cell.linearValue side.direction.step
            (normalizeVertexPosition last) + 2 <
          Cell.linearValue side.direction.step point := by
    exact unitSegmentPoints_reverse_drop_three_linearValue_gt
      side normalizedAligned
      ((between_normalizeVertexPosition last before).trans direction)
  have templateBound :
      ∀ point ∈ template,
        Cell.linearValue side.direction.step point ≤
          Cell.linearValue side.direction.step
            (normalizeVertexPosition last) + 3 := by
    exact normalizationTemplateAt_route_linearValue_le_boundary
      last omitted side used
  have prefixAvoids :=
    LocalIncidenceDrawing.RouteIsSimple.dropLast_avoids_last
      (last := last) simple (by simp)
  have initialStrict :
      RoutesStrictlyAvoidEachOther initialRoute template := by
    exact magnifiedUnitRoute_strictlyAvoids_normalizationTemplateAt_route
      prefixOrthogonal
      (by simpa [oldPrefix] using prefixAvoids.1)
      (by
        intro segment segmentMember segmentAligned
        exact prefixAvoids.2 segment
          (by simpa [oldPrefix] using segmentMember) segmentAligned)
      omitted (canonicalPortForSide omitted side)
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
    apply normalizationTemplateAt_route_eq_boundary_of_linearValue_eq
      last omitted side used point templateMember
    omega
  · have initialMember : point ∈ initialRoute :=
      List.mem_reverse.mp initialReverseMember
    exact
      (initialStrict.2.2.2 point initialMember
        point templateMember rfl).elim

/-- For one lifted contracted edge, each endpoint template shares with its
own corridor exactly the corresponding splice boundary. -/
theorem ContinuousPlanarPresentation.firstNormalizationOccurrence_onlyCommonJunctions
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
    let sourceRoute := planar.firstNormalizationTemplateOccurrence
      (.source edge) routeTranslate
    let middleRoute := planar.firstNormalizationCorridorOccurrence
      edge routeTranslate
    let targetRoute :=
      (planar.firstNormalizationTemplateOccurrence
        (.target edge) routeTranslate).reverse
    ∃ sourceBoundary targetBoundary,
      (∀ point, point ∈ sourceRoute → point ∈ middleRoute →
        point = sourceBoundary) ∧
      (∀ point, point ∈ middleRoute → point ∈ targetRoute →
        point = targetBoundary) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute :=
    planar.contractedEdgeRouteOccurrence edge routeTranslate
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourcePosition := planar.contractedEndpointOccurrencePosition
    sourceEndpoint routeTranslate
  let targetPosition := planar.contractedEndpointOccurrencePosition
    targetEndpoint routeTranslate
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    planar.contractedEdgeRouteOccurrence_length_ge_two
      degree edgeMember routeTranslate
  have oldSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    planar.contractedEdgeRouteOccurrence_isSimple
      degree separated sourceSimple edgeMember routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    planar.contractedEdgeRouteOccurrence_orthogonal
      edgeMember routeTranslate
  obtain ⟨first, second, rest, sourceEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  obtain ⟨leading, before, last, targetEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have endpoints :=
    planar.contractedEdgeRouteOccurrence_normalizationEndpoints
      edgeMember routeTranslate
  change oldRoute.head? = some sourcePosition ∧
    oldRoute.getLast? = some targetPosition at endpoints
  have firstEqual : first = sourcePosition := by
    rw [sourceEquation] at endpoints
    exact Option.some.inj endpoints.1
  have lastEqual : last = targetPosition := by
    rw [targetEquation] at endpoints
    apply Option.some.inj
    simpa using endpoints.2
  subst first
  subst last
  have targetAligned :
      (GridSegment.mk before targetPosition).IsAxisAligned := by
    rw [targetEquation] at oldOrthogonal
    exact (List.isChain_append_cons_cons.mp oldOrthogonal).2.1
  have sourceDirection :
      AxisDirection.between sourcePosition second =
        (sourceEndpoint.outwardSide planar).direction := by
    calc
      _ = AxisDirection.polylineFirstDirection oldRoute := by
        rw [sourceEquation]
        rfl
      _ = AxisDirection.polylineFirstDirection
          (planar.contractedEdgeRoute edge) := by
        simp [oldRoute, PlanarPresentation.contractedEdgeRouteOccurrence]
      _ = sourceEndpoint.outwardDirection planar := by rfl
      _ = (sourceEndpoint.outwardSide planar).direction :=
        (sourceEndpoint.outwardSide_direction
          planar degree sourceMember).symm
  have targetDirection :
      AxisDirection.between targetPosition before =
        (targetEndpoint.outwardSide planar).direction := by
    calc
      _ = (AxisDirection.polylineLastDirection oldRoute).opposite := by
        rw [targetEquation]
        rw [AxisDirection.polylineLastDirection_append_pair_of_axisAligned
          leading targetAligned]
        exact AxisDirection.between_reverse_eq_opposite
          (AxisDirection.between_isGenuine_of_axisAligned targetAligned)
      _ = (AxisDirection.polylineLastDirection
          (planar.contractedEdgeRoute edge)).opposite := by
        simp [oldRoute, PlanarPresentation.contractedEdgeRouteOccurrence]
      _ = targetEndpoint.outwardDirection planar := by rfl
      _ = (targetEndpoint.outwardSide planar).direction :=
        (targetEndpoint.outwardSide_direction
          planar degree targetMember).symm
  have sourceUsed := sourceEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree sourceMember
  have targetUsed := targetEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree targetMember
  let sourceBoundary := Cell.add (normalizeVertexPosition sourcePosition)
    (Cell.scale 3 (sourceEndpoint.outwardSide planar).direction.step)
  let targetBoundary := Cell.add (normalizeVertexPosition targetPosition)
    (Cell.scale 3 (targetEndpoint.outwardSide planar).direction.step)
  refine ⟨sourceBoundary, targetBoundary, ?_, ?_⟩
  · intro point templateMember corridorMember
    have common := trimmedMagnifiedRoute_meets_ownTemplate_onlyAt_source
      sourcePosition second rest
      (by simpa [sourceEquation] using oldSimple)
      (by simpa [sourceEquation] using oldOrthogonal)
      (sourceEndpoint.outwardSide planar) sourceDirection
      (omittedSideAt planar sourceEndpoint.vertex) sourceUsed
      point
    apply common
    · simpa [PlanarPresentation.firstNormalizationTemplateOccurrence,
        ContractedEndpoint.firstNormalizationTemplate,
        ContractedEndpoint.firstNormalizedPort,
        sourcePosition, sourceEndpoint] using templateMember
    · change point ∈ trimmedMagnifiedRoute oldRoute at corridorMember
      rw [sourceEquation] at corridorMember
      exact corridorMember
  · intro point corridorMember templateMember
    have common := trimmedMagnifiedRoute_meets_ownTemplate_onlyAt_target
      leading before targetPosition
      (by simpa [targetEquation] using oldSimple)
      (by simpa [targetEquation] using oldOrthogonal)
      (targetEndpoint.outwardSide planar) targetDirection
      (omittedSideAt planar targetEndpoint.vertex) targetUsed
      point
    apply common
    · have forwardMember : point ∈
          planar.firstNormalizationTemplateOccurrence
            targetEndpoint routeTranslate :=
        List.mem_reverse.mp templateMember
      simpa [PlanarPresentation.firstNormalizationTemplateOccurrence,
        ContractedEndpoint.firstNormalizationTemplate,
        ContractedEndpoint.firstNormalizedPort,
        targetPosition, targetEndpoint] using forwardMember
    · change point ∈ trimmedMagnifiedRoute oldRoute at corridorMember
      rw [targetEquation] at corridorMember
      exact corridorMember

/-- Every lifted first-round endpoint template is duplicate-free. -/
theorem PlanarPresentation.firstNormalizationTemplateOccurrence_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (endpointTranslate : Cell) :
    (presentation.firstNormalizationTemplateOccurrence
      endpoint endpointTranslate).Nodup := by
  unfold PlanarPresentation.firstNormalizationTemplateOccurrence
    ContractedEndpoint.firstNormalizationTemplate
  exact normalizationTemplateAt_route_nodup _ _ _

/-- Every lifted first-round middle corridor is duplicate-free. -/
theorem PlanarPresentation.firstNormalizationCorridorOccurrence_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    (presentation.firstNormalizationCorridorOccurrence
      edge routeTranslate).Nodup := by
  let oldRoute :=
    presentation.contractedEdgeRouteOccurrence edge routeTranslate
  have oldOrthogonal : OrthogonalPolyline oldRoute :=
    presentation.contractedEdgeRouteOccurrence_orthogonal
      edgeMember routeTranslate
  have oldSimple : LocalIncidenceDrawing.RouteIsSimple oldRoute :=
    presentation.contractedEdgeRouteOccurrence_isSimple
      degree separated sourceSimple edgeMember routeTranslate
  have magnifiedNodup : (magnifiedUnitRoute oldRoute).Nodup :=
    magnifiedUnitRoute_nodup oldOrthogonal oldSimple
  unfold PlanarPresentation.firstNormalizationCorridorOccurrence
    trimmedMagnifiedRoute
  have droppedNodup :
      ((magnifiedUnitRoute oldRoute).drop 3).Nodup :=
    List.Pairwise.drop magnifiedNodup
  exact droppedNodup.take

/-- Each complete lifted route produced by the first normalization splice
has no repeated listed point. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrence1_nodup
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
      |>.normalizationRouteOccurrence1 edge routeTranslate
      |>.Nodup := by
  let planar := presentation.toPlanarPresentation
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourceRoute := planar.firstNormalizationTemplateOccurrence
    sourceEndpoint routeTranslate
  let middleRoute := planar.firstNormalizationCorridorOccurrence
    edge routeTranslate
  let targetForward := planar.firstNormalizationTemplateOccurrence
    targetEndpoint routeTranslate
  let targetRoute := targetForward.reverse
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have sourceNodup : sourceRoute.Nodup :=
    planar.firstNormalizationTemplateOccurrence_nodup
      sourceEndpoint routeTranslate
  have middleNodup : middleRoute.Nodup :=
    planar.firstNormalizationCorridorOccurrence_nodup
      degree separated sourceSimple edgeMember routeTranslate
  have targetForwardNodup : targetForward.Nodup :=
    planar.firstNormalizationTemplateOccurrence_nodup
      targetEndpoint routeTranslate
  have targetNodup : targetRoute.Nodup := by
    exact targetForwardNodup.reverse.imp fun different =>
      Ne.symm different
  rcases presentation.firstNormalizationOccurrence_junctions
      wellFormed degree edgeMember routeTranslate with
    ⟨sourceBoundary, targetBoundary,
      sourceLast, middleHead, middleLast, targetHead⟩
  rcases presentation.firstNormalizationOccurrence_onlyCommonJunctions
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
  have oldRouteSimple : LocalIncidenceDrawing.RouteIsSimple
      (planar.contractedEdgeRouteOccurrence edge routeTranslate) :=
    planar.contractedEdgeRouteOccurrence_isSimple
      degree separated sourceSimple edgeMember routeTranslate
  have oldEndpoints :=
    planar.contractedEdgeRouteOccurrence_normalizationEndpoints
      edgeMember routeTranslate
  have sourcePositionNeTargetPosition :
      planar.contractedEndpointOccurrencePosition
          sourceEndpoint routeTranslate ≠
        planar.contractedEndpointOccurrencePosition
          targetEndpoint routeTranslate := by
    intro equal
    have routeLength : 2 ≤
        (planar.contractedEdgeRouteOccurrence
          edge routeTranslate).length :=
      planar.contractedEdgeRouteOccurrence_length_ge_two
        degree edgeMember routeTranslate
    obtain ⟨first, second, rest, routeEquation⟩ :=
      List.exists_eq_cons_cons_of_length_ge_two routeLength
    rw [routeEquation] at oldEndpoints oldRouteSimple
    have firstEqual : first =
        planar.contractedEndpointOccurrencePosition
          sourceEndpoint routeTranslate :=
      Option.some.inj oldEndpoints.1
    subst first
    have targetInTail :
        planar.contractedEndpointOccurrencePosition
            targetEndpoint routeTranslate ∈
          second :: rest := by
      apply List.mem_of_mem_getLast?
      change (second :: rest).getLast? = some
        (planar.contractedEndpointOccurrencePosition
          (.target edge) routeTranslate)
      rw [planar.contractedEndpointOccurrencePosition_target]
      simpa using oldEndpoints.2
    exact (List.nodup_cons.mp oldRouteSimple.1).1
      (equal ▸ targetInTail)
  have sourceTargetStrict : RoutesStrictlyAvoidEachOther
      sourceRoute targetRoute := by
    have forward : RoutesStrictlyAvoidEachOther
        sourceRoute targetForward := by
      unfold sourceRoute targetForward
        PlanarPresentation.firstNormalizationTemplateOccurrence
        ContractedEndpoint.firstNormalizationTemplate
      exact normalizationTemplateAt_routes_strictlyAvoid_of_positions_ne
        sourcePositionNeTargetPosition
        (omittedSideAt planar sourceEndpoint.vertex)
        (omittedSideAt planar targetEndpoint.vertex)
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
  rw [planar.normalizationRouteOccurrence1_eq_threePieces]
  exact List.Nodup.joinAtEndpoint_of_only_common
    sourceNodup middleTargetNodup innerHead sourceInnerOnly

/-- Every first-round normalized contracted route is geometrically simple. -/
theorem ContinuousPlanarPresentation.normalizationRoute1_isSimple
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
      (presentation.toPlanarPresentation.normalizationRoute1 edge) := by
  let planar := presentation.toPlanarPresentation
  have occurrenceNodup :=
    presentation.normalizationRouteOccurrence1_nodup
      wellFormed degree separated sourceSimple edgeMember (0, 0)
  have routeNodup : (planar.normalizationRoute1 edge).Nodup := by
    change (translatePolyline
      (planar.normalizationGridDrawing1.periodTranslation (0, 0))
      (planar.normalizationRoute1 edge)).Nodup at occurrenceNodup
    rw [show planar.normalizationGridDrawing1.periodTranslation (0, 0) =
        (0, 0) by
      simp [PeriodicGridDrawing.periodTranslation, Cell.scale],
      PeriodicOrthocrossing.translatePolyline_zero] at occurrenceNodup
    exact occurrenceNodup
  exact routeIsSimple_of_unitSteps_of_nodup
    (presentation.normalizationRoute1_unitSteps
      wellFormed degree edgeMember)
    routeNodup

/-- All routes stored in the first intermediate normalization drawing are
geometrically simple. -/
theorem ContinuousPlanarPresentation.normalizationGridDrawing1_routesSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈
        presentation.toPlanarPresentation.normalizationGridDrawing1.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  let planar := presentation.toPlanarPresentation
  intro route routeMember
  rcases List.mem_iff_get.mp routeMember with ⟨index, routeAt⟩
  have taggedMember :
      (route, index.val) ∈
        planar.normalizationGridDrawing1.edgeRoutes.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨index.isLt, routeAt⟩
  rcases planar.normalizationGridDrawing1_route_has_edge taggedMember with
    ⟨edge, edgeMember, routeEq⟩
  change route = planar.normalizationRoute1 edge at routeEq
  rw [routeEq]
  exact presentation.normalizationRoute1_isSimple
    wellFormed degree separated sourceSimple
      (List.fst_mem_of_mem_zipIdx edgeMember)

/-- Consequently the first intermediate normalization drawing has the
endpoint-only listed-point contact certificate needed by the next round. -/
theorem ContinuousPlanarPresentation.normalizationGridDrawing1_routePointsMeetOnlyAtEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.normalizationGridDrawing1
      |>.RoutePointsMeetOnlyAtEndpoints :=
  PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
    (presentation.normalizationGridDrawing1_liftedRoutesAvoidEachOther
      wellFormed degree separated sourceSimple)
    (presentation.normalizationGridDrawing1_routesSimple
      wellFormed degree separated sourceSimple)

end PeriodicThreeDM
end LeanTrominoes
