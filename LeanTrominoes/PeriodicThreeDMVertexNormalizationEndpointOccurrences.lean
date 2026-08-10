import LeanTrominoes.PeriodicThreeDMVertexNormalizationOccurrences

/-!
# Endpoint occurrences for vertex normalization

A translated contracted route has two endpoint occurrences.  Its source uses
the route's lattice translate directly, while its target uses that translate
plus the periodic edge offset.  This module packages that bookkeeping and
proves that the resulting old-scale endpoint centers are injective.

The key distinction used by the local separation proof is therefore purely
syntactic: equal occurrence keys mean the same lifted contracted vertex;
different keys give different geometric template centers.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicThreeDM

namespace ContractedEndpoint

/-- Lattice translate of the lifted vertex occurrence represented by one end
of a contracted route occurrence.  Targets include the periodic edge offset. -/
def occurrenceTranslate : ContractedEndpoint → Cell → Cell
  | .source _, routeTranslate => routeTranslate
  | .target edge, routeTranslate =>
      Cell.add edge.toPeriodicEdge.offset routeTranslate

/-- Syntactic key for the lifted contracted vertex at one route endpoint. -/
def occurrenceKey (endpoint : ContractedEndpoint)
    (routeTranslate : Cell) : PeriodicThreeDMVertex × Cell :=
  (endpoint.vertex, endpoint.occurrenceTranslate routeTranslate)

@[simp]
theorem occurrenceTranslate_source
    (edge : ContractedEdge) (routeTranslate : Cell) :
    (ContractedEndpoint.source edge).occurrenceTranslate routeTranslate =
      routeTranslate := by
  rfl

@[simp]
theorem occurrenceTranslate_target
    (edge : ContractedEdge) (routeTranslate : Cell) :
    (ContractedEndpoint.target edge).occurrenceTranslate routeTranslate =
      Cell.add edge.toPeriodicEdge.offset routeTranslate := by
  rfl

@[simp]
theorem occurrenceKey_source
    (edge : ContractedEdge) (routeTranslate : Cell) :
    (ContractedEndpoint.source edge).occurrenceKey routeTranslate =
      (edge.toPeriodicEdge.source, routeTranslate) := by
  rfl

@[simp]
theorem occurrenceKey_target
    (edge : ContractedEdge) (routeTranslate : Cell) :
    (ContractedEndpoint.target edge).occurrenceKey routeTranslate =
      (edge.toPeriodicEdge.target,
        Cell.add edge.toPeriodicEdge.offset routeTranslate) := by
  rfl

/-- For a fixed syntactic endpoint, its lifted vertex translate uniquely
determines the translate of the owning route occurrence. -/
theorem occurrenceTranslate_injective
    (endpoint : ContractedEndpoint) :
    Function.Injective endpoint.occurrenceTranslate := by
  intro first second equal
  cases endpoint with
  | source edge =>
      exact equal
  | target edge =>
      rcases edge.toPeriodicEdge.offset with ⟨offsetX, offsetY⟩
      rcases first with ⟨firstX, firstY⟩
      rcases second with ⟨secondX, secondY⟩
      simp only [occurrenceTranslate, Cell.add, Prod.mk.injEq] at equal ⊢
      omega

/-- Equal keys for the same endpoint come from the same route translate. -/
theorem occurrenceKey_injective_for_endpoint
    (endpoint : ContractedEndpoint) {first second : Cell}
    (equal : endpoint.occurrenceKey first = endpoint.occurrenceKey second) :
    first = second := by
  apply endpoint.occurrenceTranslate_injective
  exact congrArg Prod.snd equal

end ContractedEndpoint

/-- Old-scale center of the lifted contracted vertex at one endpoint of a
route occurrence. -/
def PlanarPresentation.contractedEndpointOccurrencePosition
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (routeTranslate : Cell) : Cell :=
  Cell.add
    (presentation.normalizationPosition0 endpoint.vertex)
    (presentation.contractedDrawing.periodTranslation
      (endpoint.occurrenceTranslate routeTranslate))

/-- The source endpoint center is the translated source position appearing
in the first-round splice formula. -/
@[simp]
theorem PlanarPresentation.contractedEndpointOccurrencePosition_source
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) :
    presentation.contractedEndpointOccurrencePosition
        (.source edge) routeTranslate =
      Cell.add
        (presentation.contractedDrawing.periodTranslation routeTranslate)
        (presentation.normalizationPosition0
          edge.toPeriodicEdge.source) := by
  simp [PlanarPresentation.contractedEndpointOccurrencePosition,
    ContractedEndpoint.vertex, Cell.add, add_comm]

/-- The target endpoint center is the translated offset target position
appearing in the first-round splice formula. -/
@[simp]
theorem PlanarPresentation.contractedEndpointOccurrencePosition_target
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (routeTranslate : Cell) :
    presentation.contractedEndpointOccurrencePosition
        (.target edge) routeTranslate =
      Cell.add
        (presentation.contractedDrawing.periodTranslation routeTranslate)
        (presentation.normalizationTarget0 edge) := by
  rw [show
    presentation.contractedEndpointOccurrencePosition
        (.target edge) routeTranslate =
      Cell.add
        (presentation.normalizationPosition0 edge.toPeriodicEdge.target)
        (presentation.contractedDrawing.periodTranslation
          (Cell.add edge.toPeriodicEdge.offset routeTranslate)) by
      rfl]
  rw [periodTranslation_add]
  simp [PlanarPresentation.normalizationTarget0,
    Cell.add, add_comm, add_assoc]

/-- Every listed contracted prototype vertex occupies the open fundamental
square of the contracted drawing. -/
theorem PlanarPresentation.normalizationPosition0_in_fundamental_square
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.contractedDrawing.PositionInFundamentalSquare
      (presentation.normalizationPosition0 vertex) := by
  apply presentation.contractedPositions_in_fundamental_square
  unfold PlanarPresentation.normalizationPosition0
  rw [presentation.contractedDrawing_vertexPosition member]
  rw [presentation.contractedVertexPositions_eq_map]
  exact List.mem_map.mpr ⟨vertex, member, rfl⟩

/-- Contracted prototype vertices still have distinct old-scale positions. -/
theorem PlanarPresentation.normalizationPosition0_injective_on
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : PeriodicThreeDMVertex}
    (firstMember : first ∈ problem.contractedGraph.vertices)
    (secondMember : second ∈ problem.contractedGraph.vertices)
    (equal : presentation.normalizationPosition0 first =
      presentation.normalizationPosition0 second) :
    first = second := by
  unfold PlanarPresentation.normalizationPosition0 at equal
  rw [presentation.contractedDrawing_vertexPosition firstMember,
    presentation.contractedDrawing_vertexPosition secondMember] at equal
  exact presentation.vertexPosition_injective_on
    (contractedGraph_vertex_mem_incidenceGraph problem firstMember)
    (contractedGraph_vertex_mem_incidenceGraph problem secondMember)
    equal

/-- Equal geometric endpoint centers recover the prototype vertex and its
adjusted lattice translate. -/
theorem PlanarPresentation.contractedEndpointOccurrencePosition_injective
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : ContractedEndpoint}
    (firstMember : first.vertex ∈ problem.contractedGraph.vertices)
    (secondMember : second.vertex ∈ problem.contractedGraph.vertices)
    {firstTranslate secondTranslate : Cell}
    (equal :
      presentation.contractedEndpointOccurrencePosition
          first firstTranslate =
        presentation.contractedEndpointOccurrencePosition
          second secondTranslate) :
    first.occurrenceKey firstTranslate =
      second.occurrenceKey secondTranslate := by
  have recovered :=
    PeriodicGridDrawing.fundamentalPointOccurrence_injective
      presentation.contractedDrawing
      (presentation.normalizationPosition0_in_fundamental_square firstMember)
      (presentation.normalizationPosition0_in_fundamental_square secondMember)
      equal
  exact Prod.ext
    (presentation.normalizationPosition0_injective_on
      firstMember secondMember recovered.1)
    recovered.2

/-- Distinct endpoint-occurrence keys have distinct old-scale template
centers. -/
theorem PlanarPresentation.contractedEndpointOccurrencePositions_ne
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : ContractedEndpoint}
    (firstMember : first.vertex ∈ problem.contractedGraph.vertices)
    (secondMember : second.vertex ∈ problem.contractedGraph.vertices)
    {firstTranslate secondTranslate : Cell}
    (different : first.occurrenceKey firstTranslate ≠
      second.occurrenceKey secondTranslate) :
    presentation.contractedEndpointOccurrencePosition
        first firstTranslate ≠
      presentation.contractedEndpointOccurrencePosition
        second secondTranslate := by
  intro equal
  exact different
    (presentation.contractedEndpointOccurrencePosition_injective
      firstMember secondMember equal)

end PeriodicThreeDM
end LeanTrominoes
