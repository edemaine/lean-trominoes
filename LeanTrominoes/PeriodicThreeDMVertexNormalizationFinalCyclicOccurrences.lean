import LeanTrominoes.PeriodicThreeDMVertexNormalizationCyclicRouteSimplicity
import LeanTrominoes.PeriodicThreeDMVertexNormalizationDrawing

/-!
# Lifted occurrences for the final cyclic normalization round

This module names the lifted endpoint centers, templates, corridors, and
complete routes of the third and final local replacement, and gives its exact
three-piece splice formula.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- The center of a lifted endpoint occurrence after the first cyclic round. -/
def PlanarPresentation.normalizationEndpointOccurrencePosition2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) : Cell :=
  match endpoint with
  | .source edge =>
      Cell.add
        (presentation.normalizationGridDrawing2.periodTranslation
          routeTranslate)
        (presentation.normalizationPosition2
          edge.toPeriodicEdge.source)
  | .target edge =>
      Cell.add
        (presentation.normalizationGridDrawing2.periodTranslation
          routeTranslate)
        (presentation.normalizationTarget2 edge)

/-- A second-stage endpoint center is the affine normalization of the
corresponding first-stage lifted endpoint center. -/
theorem PlanarPresentation.normalizationEndpointOccurrencePosition2_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) :
    presentation.normalizationEndpointOccurrencePosition2
        endpoint routeTranslate =
      normalizeVertexPosition
        (presentation.normalizationEndpointOccurrencePosition1
          endpoint routeTranslate) := by
  cases endpoint with
  | source edge =>
      unfold PlanarPresentation.normalizationEndpointOccurrencePosition2
        PlanarPresentation.normalizationEndpointOccurrencePosition1
        PlanarPresentation.normalizationPosition2
      rw [normalizeVertexPosition_add_left,
        presentation.normalizationGridDrawing2_periodTranslation]
  | target edge =>
      unfold PlanarPresentation.normalizationEndpointOccurrencePosition2
        PlanarPresentation.normalizationEndpointOccurrencePosition1
        PlanarPresentation.normalizationTarget2
      rw [normalizeVertexPosition_add_left,
        presentation.normalizationGridDrawing2_periodTranslation]

/-- Equal second-stage endpoint centers recover the same endpoint-occurrence
key. -/
theorem PlanarPresentation.normalizationEndpointOccurrencePosition2_injective
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : ContractedEndpoint}
    (firstMember : first.vertex ∈ problem.contractedGraph.vertices)
    (secondMember : second.vertex ∈ problem.contractedGraph.vertices)
    {firstTranslate secondTranslate : Cell}
    (equal :
      presentation.normalizationEndpointOccurrencePosition2
          first firstTranslate =
        presentation.normalizationEndpointOccurrencePosition2
          second secondTranslate) :
    first.occurrenceKey firstTranslate =
      second.occurrenceKey secondTranslate := by
  rw [presentation.normalizationEndpointOccurrencePosition2_eq,
    presentation.normalizationEndpointOccurrencePosition2_eq] at equal
  exact presentation.normalizationEndpointOccurrencePosition1_injective
    firstMember secondMember (normalizeVertexPosition_injective equal)

/-- The final cyclic template at a lifted endpoint. -/
def PlanarPresentation.finalNormalizationTemplateOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) : List Cell :=
  normalizationTemplateAt
    (presentation.normalizationEndpointOccurrencePosition2
      endpoint routeTranslate)
    (endpoint.finalNormalizationTemplate presentation)

/-- The trimmed magnified middle of a lifted second-round route. -/
def PlanarPresentation.finalNormalizationCorridorOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) : List Cell :=
  trimmedMagnifiedRoute
    (presentation.normalizationRouteOccurrence2 edge routeTranslate)

/-- A lifted complete route after all three local replacements. -/
def PlanarPresentation.finalNormalizationRouteOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) : List Cell :=
  translatePolyline
    (presentation.finalNormalizedGridDrawing.periodTranslation routeTranslate)
    (presentation.finalNormalizationRoute edge)

/-- A final period translation is the twelvefold image of the second
intermediate drawing's period translation. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_periodTranslation_eq_scale_normalizationGridDrawing2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (routeTranslate : Cell) :
    presentation.finalNormalizedGridDrawing.periodTranslation
        routeTranslate =
      Cell.scale vertexNormalizationScale
        (presentation.normalizationGridDrawing2.periodTranslation
          routeTranslate) := by
  rw [presentation.finalNormalizedGridDrawing_periodTranslation,
    ← presentation.finalScaledPeriodTranslation_eq,
    presentation.normalizationGridDrawing2_periodTranslation,
    presentation.normalizationGridDrawing1_periodTranslation,
    Cell.scale_scale, Cell.scale_scale]
  norm_num [vertexNormalizationScale]

/-- A lifted final route is the final cyclic splice applied directly to its
lifted second-round occurrence. -/
theorem PlanarPresentation.finalNormalizationRouteOccurrence_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) :
    presentation.finalNormalizationRouteOccurrence edge routeTranslate =
      normalizeRouteWithTemplates
        (Cell.add
          (presentation.normalizationGridDrawing2.periodTranslation
            routeTranslate)
          (presentation.normalizationPosition2
            edge.toPeriodicEdge.source))
        (Cell.add
          (presentation.normalizationGridDrawing2.periodTranslation
            routeTranslate)
          (presentation.normalizationTarget2 edge))
        ((ContractedEndpoint.source edge).finalNormalizationTemplate
          presentation)
        ((ContractedEndpoint.target edge).finalNormalizationTemplate
          presentation)
        (presentation.normalizationRouteOccurrence2
          edge routeTranslate) := by
  unfold PlanarPresentation.finalNormalizationRouteOccurrence
    PlanarPresentation.finalNormalizationRoute
  rw [presentation.finalNormalizedGridDrawing_periodTranslation_eq_scale_normalizationGridDrawing2]
  rw [← normalizeRouteWithTemplates_translatePolyline]
  rfl

/-- The final occurrence formula is source template, trimmed middle, and
reversed target template joined at their endpoints. -/
theorem PlanarPresentation.finalNormalizationRouteOccurrence_eq_threePieces
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) :
    presentation.finalNormalizationRouteOccurrence edge routeTranslate =
      joinAtEndpoint
        (presentation.finalNormalizationTemplateOccurrence
          (.source edge) routeTranslate)
        (joinAtEndpoint
          (presentation.finalNormalizationCorridorOccurrence
            edge routeTranslate)
          (presentation.finalNormalizationTemplateOccurrence
            (.target edge) routeTranslate).reverse) := by
  rw [presentation.finalNormalizationRouteOccurrence_eq]
  unfold normalizeRouteWithTemplates
    PlanarPresentation.finalNormalizationTemplateOccurrence
    PlanarPresentation.finalNormalizationCorridorOccurrence
    PlanarPresentation.normalizationEndpointOccurrencePosition2
  rfl

/-- The lifted second-round route preserves the endpoint centers and
adjacent unit steps consumed by the final cyclic replacement. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrence2_endpointGeometry
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let sourceEndpoint := ContractedEndpoint.source edge
    let targetEndpoint := ContractedEndpoint.target edge
    let sourcePort := sourceEndpoint.secondNormalizedPort planar
    let targetPort := targetEndpoint.secondNormalizedPort planar
    let route := planar.normalizationRouteOccurrence2 edge routeTranslate
    route.head? = some
        (planar.normalizationEndpointOccurrencePosition2
          sourceEndpoint routeTranslate) ∧
      route.tail.head? = some (Cell.add
        (planar.normalizationEndpointOccurrencePosition2
          sourceEndpoint routeTranslate)
        sourcePort.direction.step) ∧
      route.getLast? = some
        (planar.normalizationEndpointOccurrencePosition2
          targetEndpoint routeTranslate) ∧
      route.reverse.tail.head? = some (Cell.add
        (planar.normalizationEndpointOccurrencePosition2
          targetEndpoint routeTranslate)
        targetPort.direction.step) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have geometry := presentation.normalizationRoute2_endpointGeometry
    wellFormed degree edgeMember
  let offset :=
    planar.normalizationGridDrawing2.periodTranslation routeTranslate
  have tailHeadMap (items : List Cell) :
      (items.map (Cell.add offset)).tail.head? =
        items.tail.head?.map (Cell.add offset) := by
    cases items with
    | nil => rfl
    | cons first rest =>
        cases rest <;> rfl
  have reverseTailHeadMap (items : List Cell) :
      (items.map (Cell.add offset)).reverse.tail.head? =
        items.reverse.tail.head?.map (Cell.add offset) := by
    rw [← List.map_reverse]
    exact tailHeadMap items.reverse
  unfold PlanarPresentation.normalizationRouteOccurrence2
    PlanarPresentation.normalizationEndpointOccurrencePosition2
    PeriodicOrthocrossing.translatePolyline
  change
    ((planar.normalizationRoute2 edge).map
        (Cell.add offset)).head? = _ ∧
      ((planar.normalizationRoute2 edge).map
          (Cell.add offset)).tail.head? = _ ∧
      ((planar.normalizationRoute2 edge).map
          (Cell.add offset)).getLast? = _ ∧
      ((planar.normalizationRoute2 edge).map
          (Cell.add offset)).reverse.tail.head? = _
  rw [List.head?_map, tailHeadMap, List.getLast?_map,
    reverseTailHeadMap, geometry.1, geometry.2.1,
    geometry.2.2.1, geometry.2.2.2]
  simp only [Option.map_some]
  constructor <;> simp [offset, planar, Cell.add, add_assoc]

end PeriodicThreeDM
end LeanTrominoes
