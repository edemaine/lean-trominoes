/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineScaledEndpointTrimNeighborhood
import LeanTrominoes.GridPolylineRealEndpointDirections

/-! # The trimmed endpoint formulas and exclusion of original endpoints -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem clippedScaledRoute_head {route : List Cell} (long : 2 ≤ route.length) {source : Cell}
    (head : route.head? = some source) :
    (clippedScaledRoute route).head? = some
      (Cell.add (Cell.scale 32 source) (Cell.scale 8 (AxisDirection.polylineFirstDirection route).step)) := by
  cases route with
  | nil => simp at long
  | cons first rest =>
    cases rest with
    | nil => simp at long
    | cons second rest =>
      have equal : first = source := by simpa using head
      subst first
      simp [clippedScaledRoute,List.head?_mapIdx,clippedScaledPoint,AxisDirection.polylineFirstDirection]

theorem clippedScaledRoute_last {route : List Cell} (long : 2 ≤ route.length)
    (orthogonal : OrthogonalPolyline route) {target : Cell} (last : route.getLast? = some target) :
    (clippedScaledRoute route).getLast? = some
      (Cell.add (Cell.scale 32 target) (Cell.scale 8 (AxisDirection.polylineLastDirection route).opposite.step)) := by
  have positive : 0 < (gridPolylineSegments route).length := by rw [gridPolylineSegments_length]; omega
  let index := (gridPolylineSegments route).length-1
  have valid : index < (gridPolylineSegments route).length := by dsimp [index]; omega
  let segment := (gridPolylineSegments route)[index]'valid
  have member : (segment,index) ∈ (gridPolylineSegments route).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem valid]
  have lastIndex : index+1 = (gridPolylineSegments route).length := by dsimp [index]; omega
  have aligned := (orthogonalPolyline_iff_segments _).mp orthogonal segment (List.fst_mem_of_mem_zipIdx member)
  have direction := lastDirection_of_indexed_last member lastIndex aligned
  dsimp only [Prod.fst] at direction
  have endpoint : segment.finish = target :=
    Option.some.inj ((indexed_gridPolylineSegment_last member lastIndex).symm.trans last)
  have childAt := clippedScaledRoute_piece_of_indexed member
  have childMember : (segment.trimScaled (firstTrimCut index)
      (lastTrimCut (gridPolylineSegments route).length index),index) ∈
      (gridPolylineSegments (clippedScaledRoute route)).zipIdx := List.mem_zipIdx_iff_getElem?.mpr childAt
  have childLastIndex : index+1 = (gridPolylineSegments (clippedScaledRoute route)).length := by
    rw [clippedScaledRoute_segments_length]
    exact lastIndex
  have childLast := indexed_gridPolylineSegment_last childMember childLastIndex
  rw [childLast]
  congr 1
  simp only [GridSegment.trimScaled,lastTrimCut,lastIndex,ite_true]
  rw [← direction,endpoint]
  have genuine : (AxisDirection.between segment.start segment.finish).IsGenuine :=
    AxisDirection.between_isGenuine_of_axisAligned (first := segment.start) (second := segment.finish) aligned
  rw [← direction] at genuine
  cases d : AxisDirection.polylineLastDirection route <;>
    simp_all [AxisDirection.IsGenuine,AxisDirection.opposite,AxisDirection.step,Cell.add,Cell.scale]

theorem clippedScaledRoute_not_contains_scaled_endpoint {route : List Cell} (simple : IsRealSimple route)
    (orthogonal : OrthogonalPolyline route) {anchor : Cell} (endpoint : RealIsEndpoint route (realCell anchor)) :
    ¬ RealContains (clippedScaledRoute route) (realCell (Cell.scale 32 anchor)) := by
  intro contains
  have contact := clippedScaledRoute_neighborhood_contact simple orthogonal (fun _ => endpoint)
    (point := realCell (Cell.scale 32 anchor))
    (by simp [realCell,Cell.scale]) contains
  obtain ⟨side,equal⟩ := contact.2
  have cellEq := realCell_injective equal
  cases side <;> simp [Cell.add,Cell.scale,VertexSide.direction,AxisDirection.step] at cellEq

end LeanTrominoes.GridPolyline
