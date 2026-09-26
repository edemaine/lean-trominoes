/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexGeometry

/-! # Consecutive reconstructed points are precisely the stored segments -/
namespace LeanTrominoes.DelimitedDirectionDisplacement

private theorem segments_range (count : Nat) (point : Nat → Cell) :
    gridPolylineSegments ((List.range (count + 1)).map point) =
      (List.range count).map (fun i => (⟨point i, point (i+1)⟩ : GridSegment)) := by
  induction count generalizing point with
  | zero => simp [gridPolylineSegments]
  | succ count ih =>
      simpa [List.range_succ_eq_map, List.map_map, Function.comp_def, gridPolylineSegments] using
        congrArg (List.cons (⟨point 0, point 1⟩ : GridSegment)) (ih (fun i => point (i+1)))

def vertexSegment (start : Cell) (directions : List AxisDirection) (index : Nat) : GridSegment :=
  ⟨vertexPoint start directions index, vertexPoint start directions (index + 1)⟩

theorem rebuildRoute_segments (start : Cell) (directions : List AxisDirection) :
    gridPolylineSegments (Gadget.rebuildRoute start directions) =
      (List.range directions.length).map (vertexSegment start directions) := by
  rw [rebuildRoute_eq_vertices]
  exact segments_range directions.length (vertexPoint start directions)

private theorem range_zipIdx_map {A : Type} (count : Nat) (f : Nat → Nat → A) :
    (List.range count).zipIdx.map (fun p => f p.1 p.2) = (List.range count).map (fun i => f i i) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem rebuildRoute_indexedSegments (start : Cell) (directions : List AxisDirection) (routeIndex : Nat) :
    (gridPolylineSegments (Gadget.rebuildRoute start directions)).zipIdx.map
      (fun p => (⟨routeIndex, p.2, p.1⟩ : IndexedGridSegment)) =
      (List.range directions.length).map
        (fun i => (⟨routeIndex, i, vertexSegment start directions i⟩ : IndexedGridSegment)) := by
  rw [rebuildRoute_segments]
  simp only [List.zipIdx_map, List.map_map, Function.comp_def, Prod.map]
  simpa only [id_eq] using range_zipIdx_map directions.length
    (fun i j => (⟨routeIndex, j, vertexSegment start directions i⟩ : IndexedGridSegment))

theorem segmentFrame {A : Type} (count : Nat) (body : Nat → List A) :
    (List.range (count + 1)).flatMap (fun i => if i < count then body i else []) =
      (List.range count).flatMap body := by
  rw [List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, Nat.lt_irrefl, ↓reduceIte, List.flatMap_nil, List.append_nil]
  exact List.flatMap_congr (fun i hi => if_pos (List.mem_range.mp hi))

end LeanTrominoes.DelimitedDirectionDisplacement
