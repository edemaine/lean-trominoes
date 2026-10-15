/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingMixedVerticalPortOrder

/-! # Enlarged incidence fan ports preserve virtual vertical-face order -/
namespace LeanTrominoes.OrthogonalDrawingRefinement
open PeriodicOrthocrossing

theorem portBoundaryAnchor_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : drawing.DistinctPortRayKeys graph) (degree : graph.DegreeAtMost 4)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    -5 ≤ (portBoundaryAnchor graph drawing port).1 ∧ (portBoundaryAnchor graph drawing port).1 ≤ 5 ∧
      -10 ≤ (portBoundaryAnchor graph drawing port).2 ∧ (portBoundaryAnchor graph drawing port).2 ≤ 10 := by
  have valid : (incidenceAnchorIndex graph drawing port).val < (vertexAnchorProfile graph drawing port.vertex).anchors.length := by
    rw [AnchorProfile.anchors_length]
    exact incidenceAnchorIndex_valid distinct degree member
  have anchorMem : portBoundaryAnchor graph drawing port ∈ (vertexAnchorProfile graph drawing port.vertex).anchors := by
    simp only [portBoundaryAnchor,List.getElem?_eq_getElem valid,Option.getD_some]
    exact List.getElem_mem valid
  exact ((vertexAnchorProfile graph drawing port.vertex).anchors_on_boundary _ anchorMem).1

end LeanTrominoes.OrthogonalDrawingRefinement
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement RationalPerturbation GeneralVertexNormalization PeriodicOrthocrossing

theorem paddedFanSlabPort_coordinate_order {drawing : PeriodicGridDrawing} {firstPosition secondPosition firstAnchor secondAnchor : Cell}
    (firstBounds : -10 ≤ firstAnchor.2 ∧ firstAnchor.2 ≤ 10) (secondBounds : -10 ≤ secondAnchor.2 ∧ secondAnchor.2 ≤ 10)
    (ordered : firstPosition.2 < secondPosition.2) (left : Bool) :
    (drawing.paddedFanSlabPort firstPosition firstAnchor left).coordinate <
      (drawing.paddedFanSlabPort secondPosition secondAnchor left).coordinate := by
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have factorRoom : 20*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp [paddedRefinementFactor]
    omega
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have step := mul_le_mul_of_nonneg_left (by omega : firstPosition.2+1 ≤ secondPosition.2) factorPositive.le
  have firstHi := mul_le_mul_of_nonneg_left firstBounds.2 nonnegative
  have secondLo := mul_le_mul_of_nonneg_left secondBounds.1 nonnegative
  dsimp only [paddedFanSlabPort]
  nlinarith

def assignedFanSlabPort {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (tagged : PeriodicEdge Vertex × Nat) (target left : Bool) : OrthogonalBoundaryRouting.Port :=
  drawing.paddedFanSlabPort (drawing.outwardStraightSegment tagged target).start
    (portBoundaryAnchor graph drawing (endpointPort tagged target)) left

theorem same_vertex_incidence_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx)
    (secondMember : second ∈ graph.edges.zipIdx) (firstTarget secondTarget left : Bool)
    (sameVertex : (endpointPort first firstTarget).vertex = (endpointPort second secondTarget).vertex)
    (firstKey : drawing.portRayKey (endpointPort first firstTarget) =
      if left then .left (drawing.outwardStraightSegment first firstTarget).rationalSlope else
        .right (drawing.outwardStraightSegment first firstTarget).rationalSlope)
    (secondKey : drawing.portRayKey (endpointPort second secondTarget) =
      if left then .left (drawing.outwardStraightSegment second secondTarget).rationalSlope else
        .right (drawing.outwardStraightSegment second secondTarget).rationalSlope)
    (ordered : (virtualIncidencePort graph drawing first firstTarget left).coordinate <
      (virtualIncidencePort graph drawing second secondTarget left).coordinate) :
    (assignedFanSlabPort graph drawing first firstTarget left).coordinate <
      (assignedFanSlabPort graph drawing second secondTarget left).coordinate := by
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  have sameStart : (drawing.outwardStraightSegment first firstTarget).start = (drawing.outwardStraightSegment second secondTarget).start := by
    rw [outwardStraightSegment_start planar.1.1 firstMember firstTarget,
      outwardStraightSegment_start planar.1.1 secondMember secondTarget,sameVertex]
  have realOrder : (perturbedIncidenceHeight graph drawing first firstTarget left : ℝ) <
      (perturbedIncidenceHeight graph drawing second secondTarget left : ℝ) := by
    dsimp only [virtualIncidencePort] at ordered
    linarith
  have rationalOrder : perturbedIncidenceHeight graph drawing first firstTarget left <
      perturbedIncidenceHeight graph drawing second secondTarget left := by exact_mod_cast realOrder
  rw [perturbedIncidenceHeight_eq_evaluate,perturbedIncidenceHeight_eq_evaluate] at rationalOrder
  dsimp only [evaluate] at rationalOrder
  have sameY := congrArg Prod.snd sameStart
  have sameYQ : ((drawing.outwardStraightSegment first firstTarget).start.2 : ℚ) =
      (drawing.outwardStraightSegment second secondTarget).start.2 := by exact_mod_cast sameY
  have positive := columnPerturbation_positive planar straight
  have radiusPositive : (0 : Int) < crossingBound drawing.gridSize := by
    have gridPositive : 0 < drawing.gridSize := by unfold PeriodicGridDrawing.gridSize; omega
    unfold crossingBound
    positivity
  have anchorOrder : (portBoundaryAnchor graph drawing (endpointPort first firstTarget)).2 <
      (portBoundaryAnchor graph drawing (endpointPort second secondTarget)).2 := by
    cases left
    · have slopes : (drawing.outwardStraightSegment first firstTarget).rationalSlope <
          (drawing.outwardStraightSegment second secondTarget).rationalSlope := by
        simp only [Bool.false_eq_true,ite_false] at rationalOrder
        nlinarith
      exact right_portBoundaryAnchor_order distinct degree (endpointPort_mem graph firstMember firstTarget)
        (endpointPort_mem graph secondMember secondTarget) sameVertex firstKey secondKey slopes
    · have slopes : (drawing.outwardStraightSegment second secondTarget).rationalSlope <
          (drawing.outwardStraightSegment first firstTarget).rationalSlope := by
        simp only [ite_true] at rationalOrder
        nlinarith
      exact left_portBoundaryAnchor_order distinct degree (endpointPort_mem graph secondMember secondTarget)
        (endpointPort_mem graph firstMember firstTarget) sameVertex.symm secondKey firstKey slopes
  have scaled := mul_lt_mul_of_pos_left anchorOrder radiusPositive
  dsimp only [assignedFanSlabPort,paddedFanSlabPort]
  rw [sameStart]
  linarith

theorem virtualIncidencePort_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first second : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx)
    (secondMember : second ∈ graph.edges.zipIdx) (firstTarget secondTarget left : Bool)
    (sameX : (drawing.outwardStraightSegment first firstTarget).start.1 = (drawing.outwardStraightSegment second secondTarget).start.1)
    (firstKey : drawing.portRayKey (endpointPort first firstTarget) =
      if left then .left (drawing.outwardStraightSegment first firstTarget).rationalSlope else
        .right (drawing.outwardStraightSegment first firstTarget).rationalSlope)
    (secondKey : drawing.portRayKey (endpointPort second secondTarget) =
      if left then .left (drawing.outwardStraightSegment second secondTarget).rationalSlope else
        .right (drawing.outwardStraightSegment second secondTarget).rationalSlope)
    (ordered : (virtualIncidencePort graph drawing first firstTarget left).coordinate <
      (virtualIncidencePort graph drawing second secondTarget left).coordinate) :
    (assignedFanSlabPort graph drawing first firstTarget left).coordinate <
      (assignedFanSlabPort graph drawing second secondTarget left).coordinate := by
  by_cases sameVertex : (endpointPort first firstTarget).vertex = (endpointPort second secondTarget).vertex
  · exact same_vertex_incidence_coordinate_order planar degree straight firstMember secondMember firstTarget secondTarget left
      sameVertex firstKey secondKey ordered
  have realOrder : (perturbedIncidenceHeight graph drawing first firstTarget left : ℝ) <
      (perturbedIncidenceHeight graph drawing second secondTarget left : ℝ) := by
    dsimp only [virtualIncidencePort] at ordered
    linarith
  have rationalOrder : perturbedIncidenceHeight graph drawing first firstTarget left <
      perturbedIncidenceHeight graph drawing second secondTarget left := by exact_mod_cast realOrder
  rw [perturbedIncidenceHeight_eq_evaluate,perturbedIncidenceHeight_eq_evaluate,
    columnPerturbation_order_iff planar straight (mem_columnPerturbationValues_incidence (drawing := drawing) firstMember firstTarget left)
      (mem_columnPerturbationValues_incidence (drawing := drawing) secondMember secondTarget left)] at rationalOrder
  dsimp only [RationalPerturbation.Before,Prod.fst,Prod.snd] at rationalOrder
  have oldOrder : (drawing.outwardStraightSegment first firstTarget).start.2 < (drawing.outwardStraightSegment second secondTarget).start.2 := by
    rcases rationalOrder with separated | ⟨sameY,_⟩
    · exact_mod_cast separated
    · have positionEq : drawing.vertexPosition graph (endpointPort first firstTarget).vertex =
          drawing.vertexPosition graph (endpointPort second secondTarget).vertex := by
        rw [← outwardStraightSegment_start planar.1.1 firstMember firstTarget,
          ← outwardStraightSegment_start planar.1.1 secondMember secondTarget]
        exact Prod.ext sameX (by exact_mod_cast sameY)
      exact (sameVertex (planar.1.1.vertexPosition_injective_on
        (port_vertex_mem planar.1.1.1 (endpointPort_mem graph firstMember firstTarget))
        (port_vertex_mem planar.1.1.1 (endpointPort_mem graph secondMember secondTarget)) positionEq)).elim
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  have firstBounds := portBoundaryAnchor_bounds distinct degree (endpointPort_mem graph firstMember firstTarget)
  have secondBounds := portBoundaryAnchor_bounds distinct degree (endpointPort_mem graph secondMember secondTarget)
  exact paddedFanSlabPort_coordinate_order ⟨firstBounds.2.2.1,firstBounds.2.2.2⟩
    ⟨secondBounds.2.2.1,secondBounds.2.2.2⟩ oldOrder left

end LeanTrominoes.PeriodicGridDrawing
