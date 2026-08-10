import LeanTrominoes.PeriodicThreeDMVertexNormalizationRouteSimplicity

/-!
# Lifted occurrences for the first cyclic normalization round

After the direction-normalizing round, the next local replacement operates
on `normalizationGridDrawing1`.  This module names its lifted endpoint
centers, templates, corridors, and complete routes, and proves that the
second executable route is exactly the corresponding lifted three-piece
splice.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- The center of a lifted endpoint occurrence after the first local
normalization round. -/
def PlanarPresentation.normalizationEndpointOccurrencePosition1
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) : Cell :=
  match endpoint with
  | .source edge =>
      Cell.add
        (presentation.normalizationGridDrawing1.periodTranslation
          routeTranslate)
        (presentation.normalizationPosition1
          edge.toPeriodicEdge.source)
  | .target edge =>
      Cell.add
        (presentation.normalizationGridDrawing1.periodTranslation
          routeTranslate)
        (presentation.normalizationTarget1 edge)

/-- The first-stage endpoint center is the affine normalization of the
corresponding old lifted endpoint center. -/
theorem PlanarPresentation.normalizationEndpointOccurrencePosition1_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) :
    presentation.normalizationEndpointOccurrencePosition1
        endpoint routeTranslate =
      normalizeVertexPosition
        (presentation.contractedEndpointOccurrencePosition
          endpoint routeTranslate) := by
  cases endpoint with
  | source edge =>
      rw [presentation.contractedEndpointOccurrencePosition_source]
      unfold PlanarPresentation.normalizationEndpointOccurrencePosition1
        PlanarPresentation.normalizationPosition1
      rw [normalizeVertexPosition_add_left,
        presentation.normalizationGridDrawing1_periodTranslation]
  | target edge =>
      rw [presentation.contractedEndpointOccurrencePosition_target]
      unfold PlanarPresentation.normalizationEndpointOccurrencePosition1
        PlanarPresentation.normalizationTarget1
      rw [normalizeVertexPosition_add_left,
        presentation.normalizationGridDrawing1_periodTranslation]

private theorem normalizeVertexPosition_injective_cyclic :
    Function.Injective normalizeVertexPosition := by
  intro first second equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  have horizontalEqual := congrArg Prod.fst equal
  have verticalEqual := congrArg Prod.snd equal
  simp only [normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add] at horizontalEqual verticalEqual
  apply Prod.ext <;> omega

/-- Equal first-stage endpoint centers recover the same endpoint-occurrence
key. -/
theorem PlanarPresentation.normalizationEndpointOccurrencePosition1_injective
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : ContractedEndpoint}
    (firstMember : first.vertex ∈ problem.contractedGraph.vertices)
    (secondMember : second.vertex ∈ problem.contractedGraph.vertices)
    {firstTranslate secondTranslate : Cell}
    (equal :
      presentation.normalizationEndpointOccurrencePosition1
          first firstTranslate =
        presentation.normalizationEndpointOccurrencePosition1
          second secondTranslate) :
    first.occurrenceKey firstTranslate =
      second.occurrenceKey secondTranslate := by
  rw [presentation.normalizationEndpointOccurrencePosition1_eq,
    presentation.normalizationEndpointOccurrencePosition1_eq] at equal
  exact presentation.contractedEndpointOccurrencePosition_injective
    firstMember secondMember
      (normalizeVertexPosition_injective_cyclic equal)

/-- The selected first cyclic-round template at a lifted endpoint. -/
def PlanarPresentation.secondNormalizationTemplateOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) : List Cell :=
  normalizationTemplateAt
    (presentation.normalizationEndpointOccurrencePosition1
      endpoint routeTranslate)
    (endpoint.secondNormalizationTemplate presentation)

/-- The trimmed magnified middle of a lifted first-round normalized route. -/
def PlanarPresentation.secondNormalizationCorridorOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) : List Cell :=
  trimmedMagnifiedRoute
    (presentation.normalizationRouteOccurrence1 edge routeTranslate)

/-- A lifted complete route after the first cyclic-rotation replacement. -/
def PlanarPresentation.normalizationRouteOccurrence2
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) : List Cell :=
  translatePolyline
    (presentation.normalizationGridDrawing2.periodTranslation
      routeTranslate)
    (presentation.normalizationRoute2 edge)

/-- A second-stage period translation is the twelvefold image of the first
intermediate drawing's period translation. -/
theorem PlanarPresentation.normalizationGridDrawing2_periodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (routeTranslate : Cell) :
    presentation.normalizationGridDrawing2.periodTranslation
        routeTranslate =
      Cell.scale vertexNormalizationScale
        (presentation.normalizationGridDrawing1.periodTranslation
          routeTranslate) := by
  rcases routeTranslate with ⟨translateX, translateY⟩
  simp [PeriodicGridDrawing.periodTranslation,
    vertexNormalizationScale, Cell.scale]
  constructor <;> ring

/-- A lifted second-round route is the same cyclic template splice applied
directly to its lifted first-round route occurrence. -/
theorem PlanarPresentation.normalizationRouteOccurrence2_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) :
    presentation.normalizationRouteOccurrence2 edge routeTranslate =
      normalizeRouteWithTemplates
        (Cell.add
          (presentation.normalizationGridDrawing1.periodTranslation
            routeTranslate)
          (presentation.normalizationPosition1
            edge.toPeriodicEdge.source))
        (Cell.add
          (presentation.normalizationGridDrawing1.periodTranslation
            routeTranslate)
          (presentation.normalizationTarget1 edge))
        ((ContractedEndpoint.source edge).secondNormalizationTemplate
          presentation)
        ((ContractedEndpoint.target edge).secondNormalizationTemplate
          presentation)
        (presentation.normalizationRouteOccurrence1
          edge routeTranslate) := by
  unfold PlanarPresentation.normalizationRouteOccurrence2
    PlanarPresentation.normalizationRoute2
  rw [presentation.normalizationGridDrawing2_periodTranslation]
  rw [← normalizeRouteWithTemplates_translatePolyline]
  rfl

/-- The occurrence formula is source cyclic template, trimmed middle, and
reversed target cyclic template joined at their endpoints. -/
theorem PlanarPresentation.normalizationRouteOccurrence2_eq_threePieces
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) :
    presentation.normalizationRouteOccurrence2 edge routeTranslate =
      joinAtEndpoint
        (presentation.secondNormalizationTemplateOccurrence
          (.source edge) routeTranslate)
        (joinAtEndpoint
          (presentation.secondNormalizationCorridorOccurrence
            edge routeTranslate)
          (presentation.secondNormalizationTemplateOccurrence
            (.target edge) routeTranslate).reverse) := by
  rw [presentation.normalizationRouteOccurrence2_eq]
  unfold normalizeRouteWithTemplates
    PlanarPresentation.secondNormalizationTemplateOccurrence
    PlanarPresentation.secondNormalizationCorridorOccurrence
    PlanarPresentation.normalizationEndpointOccurrencePosition1
  rfl

/-- The lifted first-round route advertises precisely the endpoint centers
used by the first cyclic replacement. -/
theorem ContinuousPlanarPresentation.normalizationRouteOccurrence1_normalizationEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (routeTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    (planar.normalizationRouteOccurrence1 edge routeTranslate).head? =
        some (planar.normalizationEndpointOccurrencePosition1
          (.source edge) routeTranslate) ∧
      (planar.normalizationRouteOccurrence1 edge routeTranslate).getLast? =
        some (planar.normalizationEndpointOccurrencePosition1
          (.target edge) routeTranslate) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have endpoints := presentation.normalizationRoute1_endpointGeometry
    degree edgeMember
  unfold PlanarPresentation.normalizationRouteOccurrence1
    PlanarPresentation.normalizationEndpointOccurrencePosition1
    PeriodicOrthocrossing.translatePolyline
  simp only [List.head?_map, List.getLast?_map,
    endpoints.1, endpoints.2.2.1, Option.map_some]
  constructor <;> trivial

end PeriodicThreeDM
end LeanTrominoes
