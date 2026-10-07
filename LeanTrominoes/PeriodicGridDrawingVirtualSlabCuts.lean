/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingShiftedSeamBounds

/-! # Rational column cuts avoid all slope-biased row-seam crossings -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement RationalPerturbation

def seamAssignedSlab {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (key : Nat × Cell) : Int :=
  rationalSlab ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)
    (seamTowardLeft graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0))

def seamColumnDistances {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : List ℚ :=
  (seamCrossingCopies graph drawing 0).flatMap fun key =>
    [shiftedSeamAbscissa graph drawing key-seamAssignedSlab graph drawing key,
      (seamAssignedSlab graph drawing key : ℚ)+1-shiftedSeamAbscissa graph drawing key]

def columnCutMargin {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) : ℚ :=
  positiveMargin (seamColumnDistances graph drawing)/4

theorem columnCutMargin_positive {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) :
    0 < columnCutMargin graph drawing := by
  apply div_pos _ (by norm_num)
  apply positiveMargin_positive
  intro distance member
  obtain ⟨key,keyMember,distanceMember⟩ := List.mem_flatMap.mp member
  have bounds := shiftedSeamAbscissa_strict_slab_bounds planar straight keyMember
  change (seamAssignedSlab graph drawing key : ℚ) < shiftedSeamAbscissa graph drawing key ∧
    shiftedSeamAbscissa graph drawing key < (seamAssignedSlab graph drawing key : ℚ)+1 at bounds
  rcases List.mem_cons.mp distanceMember with rfl | member
  · exact sub_pos.mpr bounds.1
  · have same := List.mem_singleton.mp member
    rw [same]
    linarith [bounds.2]

theorem columnCutMargin_lt_half {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) :
    columnCutMargin graph drawing < 1/2 := by
  have bound := positiveMargin_le_one (seamColumnDistances graph drawing)
  unfold columnCutMargin
  linarith

theorem shiftedSeamAbscissa_inside_shrunken_slab {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {epsilon : ℚ} (positive : 0 < epsilon) (small : epsilon ≤ columnCutMargin graph drawing)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) :
    (seamAssignedSlab graph drawing key : ℚ)+epsilon < shiftedSeamAbscissa graph drawing key ∧
      shiftedSeamAbscissa graph drawing key < (seamAssignedSlab graph drawing key : ℚ)+1-epsilon := by
  have marginPositive := columnCutMargin_positive planar straight
  have leftBound : positiveMargin (seamColumnDistances graph drawing) ≤
      shiftedSeamAbscissa graph drawing key-seamAssignedSlab graph drawing key :=
    positiveMargin_le (List.mem_flatMap.mpr ⟨key,member,by simp⟩)
  have rightBound : positiveMargin (seamColumnDistances graph drawing) ≤
      (seamAssignedSlab graph drawing key : ℚ)+1-shiftedSeamAbscissa graph drawing key :=
    positiveMargin_le (List.mem_flatMap.mpr ⟨key,member,by simp⟩)
  unfold columnCutMargin at marginPositive small
  constructor <;> linarith

end LeanTrominoes.PeriodicGridDrawing
