/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

/-- The positive affine position normalization is injective. -/
theorem normalizeVertexPosition_injective :
    Function.Injective normalizeVertexPosition := by
  intro first second equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  have horizontalEqual := congrArg Prod.fst equal
  have verticalEqual := congrArg Prod.snd equal
  simp only [normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add] at horizontalEqual verticalEqual
  apply Prod.ext
  · omega
  · omega

/-- Applying the affine normalization three times remains injective on the
listed contracted vertices. -/
theorem PlanarPresentation.finalNormalizationPosition_injective_on
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {first second : PeriodicThreeDMVertex}
    (firstMember : first ∈ problem.contractedGraph.vertices)
    (secondMember : second ∈ problem.contractedGraph.vertices)
    (equal : presentation.finalNormalizationPosition first =
      presentation.finalNormalizationPosition second) :
    first = second := by
  have oldEqual : presentation.normalizationPosition0 first =
      presentation.normalizationPosition0 second :=
    normalizeVertexPosition_injective
      (normalizeVertexPosition_injective
        (normalizeVertexPosition_injective equal))
  unfold PlanarPresentation.normalizationPosition0 at oldEqual
  rw [presentation.contractedDrawing_vertexPosition firstMember,
    presentation.contractedDrawing_vertexPosition secondMember] at oldEqual
  exact presentation.vertexPosition_injective_on
    (contractedGraph_vertex_mem_incidenceGraph problem firstMember)
    (contractedGraph_vertex_mem_incidenceGraph problem secondMember)
    oldEqual

/-- Final normalized vertex positions remain duplicate-free. -/
theorem PlanarPresentation.finalNormalizedVertexPositions_nodup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedVertexPositions.Nodup := by
  rw [presentation.finalNormalizedVertexPositions_eq_map]
  apply List.Nodup.map_on
  · intro first firstMember second secondMember equal
    exact presentation.finalNormalizationPosition_injective_on
      firstMember secondMember equal
  · exact contractedGraph_vertices_nodup problem

/-- Three affine rounds send every contracted vertex from the old open
fundamental square into the enlarged open fundamental square. -/
theorem PlanarPresentation.finalNormalizedPositions_in_fundamental_square
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    ∀ position ∈ presentation.finalNormalizedVertexPositions,
      presentation.finalNormalizedGridDrawing.PositionInFundamentalSquare
        position := by
  intro position positionMember
  rw [presentation.finalNormalizedVertexPositions_eq_map] at positionMember
  rcases List.mem_map.mp positionMember with
    ⟨vertex, vertexMember, rfl⟩
  have oldPositionMember : presentation.normalizationPosition0 vertex ∈
      presentation.contractedVertexPositions := by
    unfold PlanarPresentation.normalizationPosition0
    rw [presentation.contractedDrawing_vertexPosition vertexMember]
    rw [presentation.contractedVertexPositions_eq_map]
    exact List.mem_map.mpr ⟨vertex, vertexMember, rfl⟩
  have oldBounds :=
    presentation.contractedPositions_in_fundamental_square
      _ oldPositionMember
  rcases presentation.normalizationPosition0 vertex with ⟨horizontal, vertical⟩
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare] at oldBounds ⊢
  simp only [PlanarPresentation.finalNormalizationPosition,
    PlanarPresentation.normalizationPosition2,
    PlanarPresentation.normalizationPosition1,
    normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.scale, Cell.add]
  rw [presentation.finalNormalizedGridDrawing_gridSize]
  simp only [PlanarPresentation.finalNormalizationPeriod,
    vertexNormalizationScaleNat]
  have oldGridPositive : 0 < presentation.contractedDrawing.gridSize :=
    Nat.zero_lt_succ presentation.contractedDrawing.gridSizePred
  norm_num at oldBounds ⊢
  constructor <;> omega

/-- Final normalized routes still match the source, target, and offset of
every contracted graph edge. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_routesMatch
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedGridDrawing.RoutesMatch
      problem.contractedGraph := by
  intro taggedGraphEdge graphEdgeMember
  rcases contractedGraph_edge_zipIdx problem graphEdgeMember with
    ⟨edge, edgeZipMember, edgeEquation⟩
  rw [← edgeEquation]
  have edgeMember : edge ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx edgeZipMember
  have graphEdgeListMember : edge.toPeriodicEdge ∈
      problem.contractedGraph.edges := by
    rw [edgeEquation]
    exact List.fst_mem_of_mem_zipIdx graphEdgeMember
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeListMember
  rw [presentation.finalNormalizedGridDrawing_edgeRoute edgeZipMember]
  rw [presentation.finalNormalizedGridDrawing_vertexPosition
      endpointMembers.1,
    presentation.finalNormalizedGridDrawing_vertexPosition
      endpointMembers.2]
  constructor
  · exact presentation.finalNormalizationRoute_head? edge
  · rw [presentation.finalNormalizationRoute_getLast? edge]
    rw [presentation.finalTargetOccurrence_eq edge]
    rw [presentation.finalScaledPeriodTranslation_eq]
    rw [presentation.finalNormalizedGridDrawing_periodTranslation]

/-- The packaged drawing has the expected vertex and edge list lengths. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_lengths
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedGridDrawing.vertexPositions.length =
        problem.contractedGraph.vertices.length ∧
      presentation.finalNormalizedGridDrawing.edgeRoutes.length =
        problem.contractedGraph.edges.length := by
  constructor
  · simp [PlanarPresentation.finalNormalizedGridDrawing,
      PlanarPresentation.finalNormalizedVertexPositions]
  · simp [PlanarPresentation.finalNormalizedGridDrawing, contractedGraph]

/-- The final normalized geometric data form a compatible finite periodic
drawing of the contracted graph. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_isCompatible
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedGridDrawing.IsCompatible
      problem.contractedGraph := by
  refine ⟨contractedGraph_isWellFormed problem,
    presentation.finalNormalizedGridDrawing_lengths.1,
    presentation.finalNormalizedGridDrawing_lengths.2,
    ?_, ?_, ?_⟩
  · exact presentation.finalNormalizedVertexPositions_nodup
  · exact presentation.finalNormalizedPositions_in_fundamental_square
  · exact presentation.finalNormalizedGridDrawing_routesMatch

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
