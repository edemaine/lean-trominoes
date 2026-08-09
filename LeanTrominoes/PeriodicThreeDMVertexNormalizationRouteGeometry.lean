import LeanTrominoes.PeriodicThreeDMNormalizationRasterizationCorrectness
import LeanTrominoes.OrthogonalPolylineHeadReplacement

/-!
# Endpoint geometry of normalized 3DM routes

The finite templates determine the cells immediately adjacent to every
degree-three vertex.  This module proves their initial directions and then
transports those facts through the final route splice.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

theorem Cell.add_assoc (first second third : Cell) :
    Cell.add (Cell.add first second) third =
      Cell.add first (Cell.add second third) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases third with ⟨thirdX, thirdY⟩
  simp only [Cell.add, Prod.mk.injEq]
  omega

namespace AxisDirection

/-- Joining after a route containing an edge does not change its first
directed edge. -/
theorem polylineFirstDirection_joinAtEndpoint
    {first second : List Cell}
    (length : 2 ≤ first.length) :
    polylineFirstDirection (LeanTrominoes.joinAtEndpoint first second) =
      polylineFirstDirection first := by
  cases first with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons next rest =>
          simp [LeanTrominoes.joinAtEndpoint, polylineFirstDirection]

/-- A unit cardinal step is a nondegenerate axis-aligned grid segment. -/
theorem IsUnitAxisStep.isAxisAligned
    {first second : Cell} (unit : IsUnitAxisStep first second) :
    (GridSegment.mk first second).IsAxisAligned := by
  rcases unit with ⟨direction, genuine, rfl⟩
  rcases first with ⟨horizontal, vertical⟩
  cases direction <;>
    simp_all [IsGenuine, step, Cell.add, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical]

end AxisDirection

namespace DegreeThreeVertexNormalization

/-- Every direction-normalization template initially leaves through its
named canonical port. -/
theorem route_firstDirection (omitted : VertexSide)
    (port : CanonicalVertexPort) :
    AxisDirection.polylineFirstDirection (route omitted port) =
      port.direction := by
  cases omitted <;> cases port <;> native_decide

/-- Identity rotation templates initially leave through the unchanged
canonical port. -/
theorem identityRotationRoute_firstDirection
    (port : CanonicalVertexPort) :
    AxisDirection.polylineFirstDirection (identityRotationRoute port) =
      port.direction := by
  cases port <;> native_decide

/-- Clockwise rotation templates initially leave through the new canonical
port naming the route. -/
theorem clockwiseRotationRoute_firstDirection
    (port : CanonicalVertexPort) :
    AxisDirection.polylineFirstDirection (clockwiseRotationRoute port) =
      port.direction := by
  cases port <;> native_decide

end DegreeThreeVertexNormalization

namespace PeriodicThreeDM

@[simp]
theorem side_ofAxisDirection_canonical
    (port : CanonicalVertexPort) :
    Side.ofAxisDirection port.direction = port.side := by
  cases port <;>
    rfl

/-- Both choices of a rotation round have a center endpoint, at least one
edge, unit steps, and the first direction named by the returned new port. -/
theorem rotationRoundPortAndRoute_geometry
    (active : Bool) (oldPort : CanonicalVertexPort) :
    let result := rotationRoundPortAndRoute active oldPort
    result.2.head? = some center ∧
      2 ≤ result.2.length ∧
      result.2.IsChain AxisDirection.IsUnitAxisStep ∧
      AxisDirection.polylineFirstDirection result.2 = result.1.direction := by
  cases active <;> cases oldPort <;> native_decide

/-- The second point of either rotation-round template is the unit step
through its returned new canonical port. -/
theorem rotationRoundPortAndRoute_secondPoint
    (active : Bool) (oldPort : CanonicalVertexPort) :
    let result := rotationRoundPortAndRoute active oldPort
    result.2.tail.head? =
      some (Cell.add center result.1.direction.step) := by
  cases active <;> cases oldPort <;> native_decide

/-- The final local endpoint template has the geometry advertised by the
endpoint's final normalized port. -/
theorem ContractedEndpoint.finalNormalizationTemplate_geometry
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    let template := endpoint.finalNormalizationTemplate presentation
    template.head? = some center ∧
      2 ≤ template.length ∧
      template.IsChain AxisDirection.IsUnitAxisStep ∧
      AxisDirection.polylineFirstDirection template =
        (endpoint.finalNormalizedPort presentation).direction := by
  simpa [ContractedEndpoint.finalNormalizationTemplate,
    ContractedEndpoint.finalNormalizedPort] using
    rotationRoundPortAndRoute_geometry
      (secondRotationActive presentation endpoint.vertex)
      (endpoint.secondNormalizedPort presentation)

/-- The first cyclic-round endpoint template has the same generic rotation
geometry, with the endpoint's second normalized port as output. -/
theorem ContractedEndpoint.secondNormalizationTemplate_geometry
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    let template := endpoint.secondNormalizationTemplate presentation
    template.head? = some center ∧
      2 ≤ template.length ∧
      template.IsChain AxisDirection.IsUnitAxisStep ∧
      AxisDirection.polylineFirstDirection template =
        (endpoint.secondNormalizedPort presentation).direction := by
  simpa [ContractedEndpoint.secondNormalizationTemplate,
    ContractedEndpoint.secondNormalizedPort] using
    rotationRoundPortAndRoute_geometry
      (firstRotationActive presentation endpoint.vertex)
      (endpoint.firstNormalizedPort presentation)

/-- The second point of the final endpoint template takes the unit step
through the endpoint's final normalized port. -/
theorem ContractedEndpoint.finalNormalizationTemplate_secondPoint
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    (endpoint.finalNormalizationTemplate presentation).tail.head? =
      some (Cell.add center
        (endpoint.finalNormalizedPort presentation).direction.step) := by
  simpa [ContractedEndpoint.finalNormalizationTemplate,
    ContractedEndpoint.finalNormalizedPort] using
    rotationRoundPortAndRoute_secondPoint
      (secondRotationActive presentation endpoint.vertex)
      (endpoint.secondNormalizedPort presentation)

/-- The first cyclic-round template's second point uses its returned port. -/
theorem ContractedEndpoint.secondNormalizationTemplate_secondPoint
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    (endpoint.secondNormalizationTemplate presentation).tail.head? =
      some (Cell.add center
        (endpoint.secondNormalizedPort presentation).direction.step) := by
  simpa [ContractedEndpoint.secondNormalizationTemplate,
    ContractedEndpoint.secondNormalizedPort] using
    rotationRoundPortAndRoute_secondPoint
      (firstRotationActive presentation endpoint.vertex)
      (endpoint.firstNormalizedPort presentation)

/-- Translating a center-rooted template to an old vertex position makes
the new normalized vertex position its head. -/
theorem normalizationTemplateAt_head?
    (position : Cell) {template : List Cell}
    (head : template.head? = some center) :
    (normalizationTemplateAt position template).head? =
      some (normalizeVertexPosition position) := by
  simp [normalizationTemplateAt,
    PeriodicOrthocrossing.translatePolyline, head,
    normalizeVertexPosition]

/-- Translating a template also translates its second point. -/
theorem normalizationTemplateAt_tail_head?
    (position : Cell) {template : List Cell} {next : Cell}
    (secondPoint : template.tail.head? = some next) :
    (normalizationTemplateAt position template).tail.head? =
      some (Cell.add (Cell.scale vertexNormalizationScale position) next) := by
  cases template with
  | nil => simp at secondPoint
  | cons first rest =>
      cases rest with
      | nil => simp at secondPoint
      | cons next rest =>
          simp at secondPoint
          subst next
          rfl

/-- Translation preserves the length of a local normalization template. -/
@[simp]
theorem normalizationTemplateAt_length
    (position : Cell) (template : List Cell) :
    (normalizationTemplateAt position template).length = template.length := by
  simp [normalizationTemplateAt, PeriodicOrthocrossing.translatePolyline]

/-- If the appended route contains an edge, it determines the joined
route's final point without needing a separate endpoint-matching premise. -/
theorem joinAtEndpoint_getLast?_of_second_length_ge_two
    {α : Type*} (first second : List α)
    (length : 2 ≤ second.length) :
    (LeanTrominoes.joinAtEndpoint first second).getLast? =
      second.getLast? := by
  cases second with
  | nil => simp at length
  | cons last rest =>
      cases rest with
      | nil => simp at length
      | cons next rest =>
          simp only [LeanTrominoes.joinAtEndpoint, List.tail_cons]
          exact List.getLast?_append_of_ne_nil first (by simp)

/-- Reversing and translating a center-rooted template makes the normalized
target position its final point. -/
theorem normalizationTemplateAt_reverse_getLast?
    (position : Cell) {template : List Cell}
    (head : template.head? = some center) :
    (normalizationTemplateAt position template).reverse.getLast? =
      some (normalizeVertexPosition position) := by
  rw [List.getLast?_reverse]
  exact normalizationTemplateAt_head? position head

/-- Provided the magnified middle survives endpoint trimming with an edge,
the reversed target template determines the normalized splice's target. -/
theorem normalizeRouteWithTemplates_getLast?
    (sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell)
    (middleLength : 2 ≤ (trimmedMagnifiedRoute oldRoute).length)
    (targetHead : targetTemplate.head? = some center)
    (targetLength : 2 ≤ targetTemplate.length) :
    (normalizeRouteWithTemplates sourcePosition targetPosition
        sourceTemplate targetTemplate oldRoute).getLast? =
      some (normalizeVertexPosition targetPosition) := by
  let targetRoute :=
    (normalizationTemplateAt targetPosition targetTemplate).reverse
  have targetRouteLength : 2 ≤ targetRoute.length := by
    simpa only [targetRoute, List.length_reverse,
      normalizationTemplateAt_length] using targetLength
  have innerLength :
      2 ≤ (joinAtEndpoint (trimmedMagnifiedRoute oldRoute)
        targetRoute).length := by
    simp only [joinAtEndpoint, List.length_append, List.length_tail]
    omega
  unfold normalizeRouteWithTemplates
  rw [joinAtEndpoint_getLast?_of_second_length_ge_two _ _ innerLength]
  rw [joinAtEndpoint_getLast?_of_second_length_ge_two _ _
    targetRouteLength]
  exact normalizationTemplateAt_reverse_getLast?
    targetPosition targetHead

/-! ## The magnified middle has enough room for trimming -/

/-- Normalizing both endpoints multiplies their Manhattan segment length by
twelve. -/
@[simp]
theorem segmentLength_normalizeVertexPosition
    (first second : Cell) :
    AxisDirection.segmentLength
        (normalizeVertexPosition first) (normalizeVertexPosition second) =
      12 * AxisDirection.segmentLength first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [normalizeVertexPosition, vertexNormalizationScale, center,
    Cell.scale, Cell.add, AxisDirection.segmentLength]
  have horizontal :
      12 * secondX + 3 - (12 * firstX + 3) =
        12 * (secondX - firstX) := by ring
  have vertical :
      12 * secondY + 3 - (12 * firstY + 3) =
        12 * (secondY - firstY) := by ring
  rw [horizontal, vertical, Int.natAbs_mul, Int.natAbs_mul]
  norm_num
  omega

/-- Magnifying a route whose first segment is genuine produces at least
thirteen unit-subdivision points. -/
theorem magnifiedUnitRoute_cons_cons_length_ge_thirteen
    (first second : Cell) (rest : List Cell)
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    13 ≤ (magnifiedUnitRoute (first :: second :: rest)).length := by
  have positive :=
    AxisDirection.segmentLength_positive_of_axisAligned aligned
  unfold magnifiedUnitRoute
  simp only [List.map_cons]
  rw [AxisDirection.unitSubdividePolyline]
  simp only [joinAtEndpoint, List.length_append, List.length_tail,
    AxisDirection.unitSegmentPoints_length,
    segmentLength_normalizeVertexPosition]
  omega

/-- After dropping three points from each end, a magnified genuine route
still contains at least seven points. -/
theorem trimmedMagnifiedRoute_length_ge_seven
    {points : List Cell} {first second : Cell}
    (head : points.head? = some first)
    (secondPoint : points.tail.head? = some second)
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    7 ≤ (trimmedMagnifiedRoute points).length := by
  cases points with
  | nil => simp at head
  | cons actualFirst rest =>
      cases rest with
      | nil => simp at secondPoint
      | cons actualSecond rest =>
          have firstEqual : actualFirst = first := Option.some.inj head
          have secondEqual : actualSecond = second := by
            simpa using Option.some.inj secondPoint
          subst actualFirst
          subst actualSecond
          have magnifiedLength :=
            magnifiedUnitRoute_cons_cons_length_ge_thirteen
              first second rest aligned
          unfold trimmedMagnifiedRoute
          simp only [List.length_take, List.length_drop]
          rw [Nat.min_eq_left]
          · omega
          · omega

/-- The second normalization-stage route starts at its source's second-stage
vertex position. -/
theorem PlanarPresentation.normalizationRoute2_head?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    (presentation.normalizationRoute2 edge).head? =
      some (presentation.normalizationPosition2 edge.toPeriodicEdge.source) := by
  unfold PlanarPresentation.normalizationRoute2
  unfold normalizeRouteWithTemplates
  apply joinAtEndpoint_head?
  apply normalizationTemplateAt_head?
  exact (ContractedEndpoint.secondNormalizationTemplate_geometry
    presentation (ContractedEndpoint.source edge)).1

/-- Its second point is the unit step through the source endpoint's
second-stage canonical port. -/
theorem PlanarPresentation.normalizationRoute2_tail_head?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    (presentation.normalizationRoute2 edge).tail.head? =
      some (Cell.add
        (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
        ((ContractedEndpoint.source edge).secondNormalizedPort
          presentation).direction.step) := by
  unfold PlanarPresentation.normalizationRoute2
  unfold normalizeRouteWithTemplates
  apply joinAtEndpoint_tail_head?
  rw [normalizationTemplateAt_tail_head?
    (secondPoint :=
      (ContractedEndpoint.source edge).secondNormalizationTemplate_secondPoint
        presentation)]
  simp [PlanarPresentation.normalizationPosition2,
    normalizeVertexPosition, Cell.add_assoc]

/-- Consequently the middle used in the final normalization round survives
trimming with at least seven points. -/
theorem PlanarPresentation.finalTrimmedMiddle_length_ge_seven
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    7 ≤ (trimmedMagnifiedRoute
      (presentation.normalizationRoute2 edge)).length := by
  let source :=
    presentation.normalizationPosition2 edge.toPeriodicEdge.source
  let direction :=
    ((ContractedEndpoint.source edge).secondNormalizedPort
      presentation).direction
  apply trimmedMagnifiedRoute_length_ge_seven
    (first := source) (second := Cell.add source direction.step)
  · exact presentation.normalizationRoute2_head? edge
  · exact presentation.normalizationRoute2_tail_head? edge
  · apply AxisDirection.IsUnitAxisStep.isAxisAligned
    exact ⟨direction, CanonicalVertexPort.direction_isGenuine _, rfl⟩

/-- The final normalized route reaches the final normalized occurrence of
its stored periodic target. -/
theorem PlanarPresentation.finalNormalizationRoute_getLast?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    (presentation.finalNormalizationRoute edge).getLast? =
      some (normalizeVertexPosition
        (presentation.normalizationTarget2 edge)) := by
  unfold PlanarPresentation.finalNormalizationRoute
  apply normalizeRouteWithTemplates_getLast?
  · exact le_trans (by omega)
      (presentation.finalTrimmedMiddle_length_ge_seven edge)
  · exact (ContractedEndpoint.finalNormalizationTemplate_geometry
      presentation (ContractedEndpoint.target edge)).1
  · exact (ContractedEndpoint.finalNormalizationTemplate_geometry
      presentation (ContractedEndpoint.target edge)).2.1

/-- The final normalized route starts at its source's final normalized
vertex position. -/
theorem PlanarPresentation.finalNormalizationRoute_head?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    (presentation.finalNormalizationRoute edge).head? =
      some (presentation.finalNormalizationPosition
        edge.toPeriodicEdge.source) := by
  unfold PlanarPresentation.finalNormalizationRoute
  unfold normalizeRouteWithTemplates
  apply joinAtEndpoint_head?
  apply normalizationTemplateAt_head?
  exact (ContractedEndpoint.finalNormalizationTemplate_geometry
    presentation (ContractedEndpoint.source edge)).1

/-- The point after the final route's source is the unit step through that
endpoint's final canonical port. -/
theorem PlanarPresentation.finalNormalizationRoute_tail_head?
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    (presentation.finalNormalizationRoute edge).tail.head? =
      some (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        ((ContractedEndpoint.source edge).finalNormalizedPort
          presentation).direction.step) := by
  unfold PlanarPresentation.finalNormalizationRoute
  unfold normalizeRouteWithTemplates
  apply joinAtEndpoint_tail_head?
  rw [normalizationTemplateAt_tail_head?
    (secondPoint :=
      (ContractedEndpoint.source edge).finalNormalizationTemplate_secondPoint
        presentation)]
  simp [PlanarPresentation.finalNormalizationPosition,
    normalizeVertexPosition, Cell.add_assoc]

/-- The source-adjacent geometric route point projects to the finite
drawing neighbor on the endpoint's canonical side. -/
theorem PlanarPresentation.normalizedPositionAt_sourceAdjacent
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    presentation.normalizedPositionAt
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step) =
      presentation.normalizedOrthogonalDrawing.neighbor
        (presentation.normalizedPositionAt
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source))
        ((ContractedEndpoint.source edge).finalNormalizedPort
          presentation).side := by
  rw [presentation.normalizedPositionAt_add_step]
  · simp
  · exact CanonicalVertexPort.direction_isGenuine _

/-- The first edge of the final route leaves through the source endpoint's
final canonical port. -/
theorem PlanarPresentation.finalNormalizationRoute_firstDirection
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    AxisDirection.polylineFirstDirection
        (presentation.finalNormalizationRoute edge) =
      ((ContractedEndpoint.source edge).finalNormalizedPort
        presentation).direction := by
  let endpoint := ContractedEndpoint.source edge
  have geometry := endpoint.finalNormalizationTemplate_geometry presentation
  unfold PlanarPresentation.finalNormalizationRoute
  unfold normalizeRouteWithTemplates
  rw [AxisDirection.polylineFirstDirection_joinAtEndpoint]
  · unfold normalizationTemplateAt
    rw [AxisDirection.polylineFirstDirection_translatePolyline]
    exact geometry.2.2.2
  · simpa using geometry.2.1

end PeriodicThreeDM
end LeanTrominoes
