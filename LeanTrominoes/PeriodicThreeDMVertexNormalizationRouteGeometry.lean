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
