/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealTube
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineJoin
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPointBounds

/-! # Orthogonal interpolation inside coordinate tubes

Joining horizontal-then-vertical elbows preserves advertised endpoints.
Bounds on the sampled points and elbow corners control the complete real
image of the resulting route, including the interiors of its segments.
-/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

/-- A horizontal-then-vertical connection, omitting constant pieces. -/
def elbow (first last : Cell) : List Cell :=
  if first = last then [first]
  else if first.1 = last.1 ∨ first.2 = last.2 then [first,last]
  else [first,(last.1,first.2),last]

@[simp] theorem elbow_head (first last : Cell) :
    (elbow first last).head? = some first := by
  unfold elbow
  split_ifs <;> rfl

@[simp] theorem elbow_last (first last : Cell) :
    (elbow first last).getLast? = some last := by
  unfold elbow
  split_ifs <;> simp_all

theorem elbow_orthogonal (first last : Cell) : OrthogonalPolyline (elbow first last) := by
  unfold elbow
  split_ifs with equal aligned
  · simp [OrthogonalPolyline]
  · rcases aligned with sameX | sameY
    · have differentY : first.2 ≠ last.2 := by
        intro sameY
        exact equal (Prod.ext sameX sameY)
      simp [OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsVertical,sameX,differentY]
    · have differentX : first.1 ≠ last.1 := by
        intro sameX
        exact equal (Prod.ext sameX sameY)
      simp [OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,sameY,differentX]
  · have differentX : first.1 ≠ last.1 := fun same => aligned (Or.inl same)
    have differentY : first.2 ≠ last.2 := fun same => aligned (Or.inr same)
    simp [OrthogonalPolyline,GridSegment.IsAxisAligned,GridSegment.IsHorizontal,
      GridSegment.IsVertical,differentX,differentY]

theorem elbow_member {first last point : Cell} (member : point ∈ elbow first last) :
    point = first ∨ point = last ∨ point = (last.1,first.2) := by
  unfold elbow at member
  split_ifs at member <;> simp_all <;> tauto

/-- Replace successive sample pairs by elbows, sharing each intermediate
sample exactly once. Repeated samples add no constant segment. -/
def rectilinearize : List Cell → List Cell
  | [] => []
  | [point] => [point]
  | first::second::rest => joinPolylines (elbow first second) (rectilinearize (second::rest))

@[simp] theorem rectilinearize_head (points : List Cell) :
    (rectilinearize points).head? = points.head? := by
  induction points using List.twoStepInduction with
  | nil => rfl
  | singleton point => rfl
  | cons_cons first second rest _ _ =>
      exact joinAtEndpoint_head? (elbow_head first second)

@[simp] theorem rectilinearize_last (points : List Cell) :
    (rectilinearize points).getLast? = points.getLast? := by
  induction points using List.twoStepInduction with
  | nil => rfl
  | singleton point => rfl
  | cons_cons first second rest _ induction =>
      have head : (rectilinearize (second::rest)).head? = some second :=
        rectilinearize_head (second::rest)
      obtain ⟨last,lastAt⟩ : ∃ last, (second::rest).getLast? = some last := by
        cases rest with
        | nil => exact ⟨second,rfl⟩
        | cons next tail => exact ⟨(second::next::tail).getLast (by simp),
            List.getLast?_eq_getLast_of_ne_nil (by simp)⟩
      have tailLast := (induction second).trans lastAt
      exact (joinAtEndpoint_getLast? (elbow_last first second) head tailLast).trans
        (by simpa only [List.getLast?_cons_cons] using lastAt.symm)

theorem rectilinearize_orthogonal (points : List Cell) : OrthogonalPolyline (rectilinearize points) := by
  induction points using List.twoStepInduction with
  | nil => simp [rectilinearize,OrthogonalPolyline]
  | singleton point => simp [rectilinearize,OrthogonalPolyline]
  | cons_cons first second rest _ induction =>
      exact (elbow_orthogonal first second).joinAtEndpoint (induction second)
        (elbow_last first second) (rectilinearize_head (second::rest))

theorem rectilinearize_points_property {property : Cell → Prop} {points : List Cell}
    (vertices : ∀ point ∈ points, property point)
    (corners : ∀ piece ∈ gridPolylineSegments points, property (piece.finish.1,piece.start.2)) :
    ∀ point ∈ rectilinearize points, property point := by
  induction points using List.twoStepInduction with
  | nil => simp [rectilinearize]
  | singleton point => simpa only [rectilinearize] using vertices
  | cons_cons first second rest _ induction =>
      intro point member
      simp only [rectilinearize,joinPolylines,List.mem_append] at member
      rcases member with elbowMember | tailMember
      · rcases elbow_member elbowMember with equal | equal | equal
        · rw [equal]
          exact vertices first (by simp)
        · rw [equal]
          exact vertices second (by simp)
        · rw [equal]
          exact corners ⟨first,second⟩ (by simp [gridPolylineSegments])
      · exact induction second
          (fun point member => vertices point (List.mem_cons_of_mem first member))
          (fun piece member => corners piece (by simp only [gridPolylineSegments,List.mem_cons]; exact Or.inr member))
          point (List.mem_of_mem_tail tailMember)

theorem rectilinearize_points_tube {segment : GridSegment} {radius : ℝ} {points : List Cell}
    (vertices : ∀ point ∈ points, segment.RealTubeContains radius (realCell point))
    (corners : ∀ piece ∈ gridPolylineSegments points,
      segment.RealTubeContains radius (realCell (piece.finish.1,piece.start.2))) :
    ∀ point ∈ rectilinearize points, segment.RealTubeContains radius (realCell point) :=
  rectilinearize_points_property vertices corners

theorem realContains_tube_of_points {segment : GridSegment} {radius : ℝ} {route : List Cell}
    (vertices : ∀ point ∈ route, segment.RealTubeContains radius (realCell point))
    {point : ℝ × ℝ} (contains : RealContains route point) : segment.RealTubeContains radius point := by
  obtain ⟨piece,pieceMember,pieceContains⟩ := contains
  have endpoints := gridPolylineSegments_endpoints_mem pieceMember
  exact (vertices piece.start endpoints.1).segment (vertices piece.finish endpoints.2) pieceContains

theorem rectilinearize_realContains_tube {segment : GridSegment} {radius : ℝ} {points : List Cell}
    (vertices : ∀ point ∈ points, segment.RealTubeContains radius (realCell point))
    (corners : ∀ piece ∈ gridPolylineSegments points,
      segment.RealTubeContains radius (realCell (piece.finish.1,piece.start.2)))
    {point : ℝ × ℝ} (contains : RealContains (rectilinearize points) point) :
    segment.RealTubeContains radius point :=
  realContains_tube_of_points (rectilinearize_points_tube vertices corners) contains

end LeanTrominoes.GridPolyline
