/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationEndpointRays

/-! # Planarity and route simplicity force distinct directions at every vertex -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing

theorem endpoint_same_direction_same_occurrence {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    (aTarget bTarget : Bool) (sameVertex : (endpointPort a aTarget).vertex = (endpointPort b bTarget).vertex)
    (sameDirection : portDirection drawing (endpointPort a aTarget) = portDirection drawing (endpointPort b bTarget)) :
    (a.2,endpointCell a aTarget) = (b.2,endpointCell b bTarget) := by
  by_contra different
  have firstContains := endpoint_ray_contains planar.1 orthogonal am aTarget
  have secondContains := endpoint_ray_contains planar.1 orthogonal bm bTarget
  rw [← sameVertex,← sameDirection] at secondContains
  have firstValid : a.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx am
  have secondValid : b.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx bm
  have endpoints := planar.2 a.2 b.2 (endpointCell a aTarget) (endpointCell b bTarget)
    firstValid secondValid different _ firstContains secondContains
  exact GridPolyline.realHalfStep_not_endpoint _ _
    (portDirection_genuine planar.1 orthogonal (endpointPort_mem graph am aTarget)) endpoints.1

theorem loop_equal_rays_impossible {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (sameVertex : tagged.1.source = tagged.1.target) (zeroOffset : tagged.1.offset = (0,0))
    (equal : AxisDirection.polylineFirstDirection (drawing.edgeRoute tagged.2) =
      (AxisDirection.polylineLastDirection (drawing.edgeRoute tagged.2)).opposite) : False := by
  have routeMember := PeriodicGridDrawing.edgeRoute_mem_of_compatible valid.1 member
  have simple := valid.2.1 _ routeMember
  have routeOrthogonal := (PeriodicGridDrawing.isOrthogonal_iff_routes _).mp orthogonal _ routeMember
  have routeMatches := valid.1.2.2.2.2.2 tagged member
  have last : (drawing.edgeRoute tagged.2).getLast? = some (drawing.vertexPosition graph tagged.1.source) := by
    simpa [← sameVertex,zeroOffset,PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add] using routeMatches.2
  exact simple.closed_endpoint_directions_ne routeOrthogonal routeMatches.1 last equal

theorem endpoint_same_side_eq {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    (aTarget bTarget : Bool) (sameVertex : (endpointPort a aTarget).vertex = (endpointPort b bTarget).vertex)
    (sameSide : portSide drawing (endpointPort a aTarget) = portSide drawing (endpointPort b bTarget)) :
    endpointPort a aTarget = endpointPort b bTarget := by
  have firstSide := portSide_direction planar.1 orthogonal (endpointPort_mem graph am aTarget)
  have secondSide := portSide_direction planar.1 orthogonal (endpointPort_mem graph bm bTarget)
  have sameDirection := firstSide.symm.trans ((congrArg VertexSide.direction sameSide).trans secondSide)
  have occurrences := endpoint_same_direction_same_occurrence planar orthogonal am bm aTarget bTarget sameVertex sameDirection
  have indices : a.2 = b.2 := congrArg Prod.fst occurrences
  have firstAt := List.mem_zipIdx_iff_getElem?.mp am
  have secondAt := List.mem_zipIdx_iff_getElem?.mp bm
  rw [← indices] at secondAt
  have edges := Option.some.inj (firstAt.symm.trans secondAt)
  have tags : a = b := Prod.ext edges indices
  subst b
  have cells := congrArg Prod.snd occurrences
  cases aTarget <;> cases bTarget
  · rfl
  · have zero : a.1.offset = (0,0) := by
      have hx := congrArg Prod.fst cells
      have hy := congrArg Prod.snd cells
      simp [endpointCell,Cell.scale] at hx hy
      exact Prod.ext (by omega) (by omega)
    exact (loop_equal_rays_impossible planar.1 orthogonal am sameVertex zero sameDirection).elim
  · have zero : a.1.offset = (0,0) := by
      have hx := congrArg Prod.fst cells
      have hy := congrArg Prod.snd cells
      simp [endpointCell,Cell.scale] at hx hy
      exact Prod.ext (by omega) (by omega)
    exact (loop_equal_rays_impossible planar.1 orthogonal am sameVertex.symm zero sameDirection.symm).elim
  · rfl

theorem distinctPortSides_of_planar_orthogonal {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal) :
    DistinctPortSides drawing graph := by
  intro first firstMember second secondMember sameVertex sameSide
  obtain ⟨a,am,firstKind⟩ := allPorts_has_edge firstMember
  obtain ⟨b,bm,secondKind⟩ := allPorts_has_edge secondMember
  rcases firstKind with rfl | rfl <;> rcases secondKind with rfl | rfl
  · exact endpoint_same_side_eq planar orthogonal am bm false false sameVertex sameSide
  · exact endpoint_same_side_eq planar orthogonal am bm false true sameVertex sameSide
  · exact endpoint_same_side_eq planar orthogonal am bm true false sameVertex sameSide
  · exact endpoint_same_side_eq planar orthogonal am bm true true sameVertex sameSide

end LeanTrominoes.GeneralVertexNormalization
