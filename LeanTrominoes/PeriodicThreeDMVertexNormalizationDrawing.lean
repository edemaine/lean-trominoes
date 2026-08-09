import LeanTrominoes.PeriodicGridDrawingUnitSubdivision
import LeanTrominoes.PeriodicThreeDMVertexNormalizationRouteValidity

/-!
# The final normalized periodic grid drawing

The rasterizer consumes the three-round normalized vertex positions and edge
routes as separate lists.  This module packages the same data as a
`PeriodicGridDrawing`, so the global collision proof can use the standard
indexed point-occurrence and separation interfaces.
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- Final normalized vertex positions in contracted-graph presentation
order. -/
def PlanarPresentation.finalNormalizedVertexPositions
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : List Cell :=
  problem.contractedGraph.vertices.zipIdx.map fun tagged =>
    presentation.finalNormalizationPosition tagged.1

/-- The geometric periodic drawing represented by the final normalized
vertex positions and routes, before compiling them into orthogonal cells. -/
def PlanarPresentation.finalNormalizedGridDrawing
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : PeriodicGridDrawing where
  gridSizePred := presentation.finalNormalizationPeriod - 1
  vertexPositions := presentation.finalNormalizedVertexPositions
  edgeRoutes := problem.contractedEdges.zipIdx.map fun tagged =>
    presentation.finalNormalizationRoute tagged.1

/-- The normalized drawing's actual period is the three-round raster
period. -/
@[simp]
theorem PlanarPresentation.finalNormalizedGridDrawing_gridSize
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedGridDrawing.gridSize =
      presentation.finalNormalizationPeriod := by
  have positive := presentation.finalNormalizationPeriod_pos
  simp [PlanarPresentation.finalNormalizedGridDrawing,
    PeriodicGridDrawing.gridSize,
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt positive))]

/-- Its period translation is scaling by the final normalization period. -/
@[simp]
theorem PlanarPresentation.finalNormalizedGridDrawing_periodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (translation : Cell) :
    presentation.finalNormalizedGridDrawing.periodTranslation translation =
      Cell.scale (presentation.finalNormalizationPeriod : Int) translation := by
  simp [PeriodicGridDrawing.periodTranslation]

/-- The zip-index implementation of final vertex positions is extensionally
the direct map used by the rasterizer. -/
theorem PlanarPresentation.finalNormalizedVertexPositions_eq_map
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedVertexPositions =
      problem.contractedGraph.vertices.map
        presentation.finalNormalizationPosition := by
  unfold PlanarPresentation.finalNormalizedVertexPositions
  calc
    _ = (problem.contractedGraph.vertices.zipIdx.map Prod.fst).map
          presentation.finalNormalizationPosition := by
      rw [List.map_map]
      rfl
    _ = _ := by rw [List.zipIdx_map_fst]

/-- Final edge routes likewise occur in contracted-edge presentation
order. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_edgeRoutes_eq_map
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedGridDrawing.edgeRoutes =
      problem.contractedEdges.map presentation.finalNormalizationRoute := by
  unfold PlanarPresentation.finalNormalizedGridDrawing
  calc
    _ = (problem.contractedEdges.zipIdx.map Prod.fst).map
          presentation.finalNormalizationRoute := by
      rw [List.map_map]
      rfl
    _ = _ := by rw [List.zipIdx_map_fst]

/-- Vertex lookup in the packaged drawing recovers the corresponding final
normalized position. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_vertexPosition
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.finalNormalizedGridDrawing.vertexPosition
        problem.contractedGraph vertex =
      presentation.finalNormalizationPosition vertex := by
  have indexLt : problem.contractedGraph.vertices.idxOf vertex <
      problem.contractedGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr member
  have taggedMember :
      (vertex, problem.contractedGraph.vertices.idxOf vertex) ∈
        problem.contractedGraph.vertices.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨indexLt, List.idxOf_get indexLt⟩
  unfold PeriodicGridDrawing.vertexPosition
    PlanarPresentation.finalNormalizedGridDrawing
    PlanarPresentation.finalNormalizedVertexPositions
  exact PeriodicOrthocrossing.getD_map_zipIdx_of_mem
    problem.contractedGraph.vertices
    (fun tagged => presentation.finalNormalizationPosition tagged.1)
    (0, 0) taggedMember

/-- Indexed edge lookup in the packaged drawing recovers the corresponding
final normalized route. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_edgeRoute
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tagged : ContractedEdge × Nat}
    (member : tagged ∈ problem.contractedEdges.zipIdx) :
    presentation.finalNormalizedGridDrawing.edgeRoute tagged.2 =
      presentation.finalNormalizationRoute tagged.1 := by
  unfold PeriodicGridDrawing.edgeRoute
    PlanarPresentation.finalNormalizedGridDrawing
  exact PeriodicOrthocrossing.getD_map_zipIdx_of_mem
    problem.contractedEdges
    (fun tagged => presentation.finalNormalizationRoute tagged.1)
    [] member

/-- Every route stored by the packaged final drawing consists of unit axis
steps. -/
theorem ContinuousPlanarPresentation.finalNormalizedGridDrawing_hasUnitSteps
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree) :
    presentation.toPlanarPresentation.finalNormalizedGridDrawing.HasUnitSteps := by
  intro route routeMember
  rw [presentation.toPlanarPresentation
    |>.finalNormalizedGridDrawing_edgeRoutes_eq_map] at routeMember
  rcases List.mem_map.mp routeMember with ⟨edge, edgeMember, routeEqual⟩
  subst route
  exact presentation.finalNormalizationRoute_unitSteps
    wellFormed degree edgeMember

end PeriodicThreeDM
end LeanTrominoes
