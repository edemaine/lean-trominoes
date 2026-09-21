/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingExpandedFiniteContinuousPlanarity

/-! # Finite translation bounds for arbitrary supplied periodic drawings -/
namespace LeanTrominoes.PeriodicGridDrawing.FiniteBounds
open PeriodicOrthocrossing

def InBox (radius : Nat) (p : Cell) : Prop :=
  -(radius : Int) ≤ p.1 ∧ p.1 ≤ radius ∧ -(radius : Int) ≤ p.2 ∧ p.2 ≤ radius

def points (drawing : PeriodicGridDrawing) : List Cell :=
  drawing.vertexPositions ++ drawing.indexedSegments.flatMap (fun s => [s.segment.start,s.segment.finish])

def radius (drawing : PeriodicGridDrawing) : Nat :=
  ((points drawing).map (fun p => p.1.natAbs + p.2.natAbs)).sum

private theorem member_le_sum (values : List Nat) (n : Nat) (h : n ∈ values) : n ≤ values.sum := by
  induction values with
  | nil => simp at h
  | cons v vs ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem point_bound (drawing : PeriodicGridDrawing) (p : Cell) (h : p ∈ points drawing) :
    InBox (radius drawing) p := by
  have hsum := member_le_sum _ _ (List.mem_map.mpr ⟨p,h,rfl⟩ :
    p.1.natAbs+p.2.natAbs ∈ (points drawing).map (fun p => p.1.natAbs+p.2.natAbs))
  change p.1.natAbs+p.2.natAbs ≤ radius drawing at hsum
  have px : p.1 ≤ (p.1.natAbs : Int) := Int.le_natAbs
  have nx : -p.1 ≤ ((-p.1).natAbs : Int) := Int.le_natAbs
  have py : p.2 ≤ (p.2.natAbs : Int) := Int.le_natAbs
  have ny : -p.2 ≤ ((-p.2).natAbs : Int) := Int.le_natAbs
  simp only [Int.natAbs_neg] at nx ny
  unfold InBox
  omega

theorem vertex_bound (drawing : PeriodicGridDrawing) (p : Cell) (h : p ∈ drawing.vertexPositions) :
    InBox (radius drawing) p := point_bound drawing p (List.mem_append_left _ h)

theorem segment_bounds (drawing : PeriodicGridDrawing) (s : IndexedGridSegment)
    (h : s ∈ drawing.indexedSegments) :
    InBox (radius drawing) s.segment.start ∧ InBox (radius drawing) s.segment.finish := by
  constructor <;> apply point_bound
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s,h,by simp⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨s,h,by simp⟩)

/-- Bounding rectangles overlap whenever the segment interiors meet. -/
def RectanglesMeet (a b : GridSegment) : Prop :=
  min a.start.1 a.finish.1 ≤ max b.start.1 b.finish.1 ∧
  min b.start.1 b.finish.1 ≤ max a.start.1 a.finish.1 ∧
  min a.start.2 a.finish.2 ≤ max b.start.2 b.finish.2 ∧
  min b.start.2 b.finish.2 ≤ max a.start.2 a.finish.2

theorem rectangles_of_interiors (a b : GridSegment) (h : GridSegment.InteriorsMeet a b) :
    RectanglesMeet a b := by
  simp only [GridSegment.InteriorsMeet,GridSegment.IsHorizontal,GridSegment.IsVertical,
    GridSegment.OpenIntervalsOverlap,GridSegment.StrictlyBetween,RectanglesMeet] at *
  omega

theorem rectangles_of_contact (a b : GridSegment) (p : Cell)
    (ha : a.InteriorContains p) (hb : b.Contains p) : RectanglesMeet a b := by
  simp only [GridSegment.InteriorContains,GridSegment.Contains,GridSegment.IsHorizontal,
    GridSegment.IsVertical,GridSegment.StrictlyBetween,GridSegment.Between,RectanglesMeet] at *
  omega

theorem rectangles_of_vertex (a : GridSegment) (p : Cell) (h : a.InteriorContains p) :
    RectanglesMeet a ⟨p,p⟩ := by
  simp only [GridSegment.InteriorContains,GridSegment.IsHorizontal,GridSegment.IsVertical,
    GridSegment.StrictlyBetween,RectanglesMeet] at *
  omega

private theorem scalar_bound (r : Nat) (period shift a b c d : Int)
    (hp : 0 < period) (ha : -(r:Int) ≤ a ∧ a ≤ r) (hb : -(r:Int) ≤ b ∧ b ≤ r)
    (hc : -(r:Int) ≤ c ∧ c ≤ r) (hd : -(r:Int) ≤ d ∧ d ≤ r)
    (overlap : min (a+period*shift) (b+period*shift) ≤ max c d ∧
      min c d ≤ max (a+period*shift) (b+period*shift)) :
    -(2*(r:Int)) ≤ shift ∧ shift ≤ 2*(r:Int) := by
  rw [min_add_add_right,max_add_add_right] at overlap
  have product : -(2*(r:Int)) ≤ period*shift ∧ period*shift ≤ 2*(r:Int) := by omega
  constructor
  · by_contra h
    have hs : shift < 0 := by omega
    have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ period-1 by omega) (le_of_lt hs)
    nlinarith
  · by_contra h
    have hs : 0 < shift := by omega
    have := mul_nonneg (show 0 ≤ period-1 by omega) (le_of_lt hs)
    nlinarith

theorem relative_bound (drawing : PeriodicGridDrawing) (a b : GridSegment) (t : Cell)
    (ha : InBox (radius drawing) a.start ∧ InBox (radius drawing) a.finish)
    (hb : InBox (radius drawing) b.start ∧ InBox (radius drawing) b.finish)
    (meet : RectanglesMeet (a.translate (drawing.periodTranslation t)) b) :
    InBox (2*radius drawing) t := by
  have hp : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  rcases ha with ⟨⟨ax,ax',ay,ay'⟩,⟨bx,bx',by_,by'⟩⟩
  rcases hb with ⟨⟨cx,cx',cy,cy'⟩,⟨dx,dx',dy,dy'⟩⟩
  simp only [RectanglesMeet,GridSegment.translate,periodTranslation,Cell.scale,Cell.add] at meet
  have x := scalar_bound (radius drawing) drawing.gridSize t.1 a.start.1 a.finish.1 b.start.1 b.finish.1
    hp ⟨ax,ax'⟩ ⟨bx,bx'⟩ ⟨cx,cx'⟩ ⟨dx,dx'⟩ (by simpa [Int.add_comm] using And.intro meet.1 meet.2.1)
  have y := scalar_bound (radius drawing) drawing.gridSize t.2 a.start.2 a.finish.2 b.start.2 b.finish.2
    hp ⟨ay,ay'⟩ ⟨by_,by'⟩ ⟨cy,cy'⟩ ⟨dy,dy'⟩ (by simpa [Int.add_comm] using meet.2.2)
  simpa [InBox,Nat.cast_mul] using And.intro x.1 (And.intro x.2 y)

end LeanTrominoes.PeriodicGridDrawing.FiniteBounds
