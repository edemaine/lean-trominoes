/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingHorizontalCrossingDistinctness
import LeanTrominoes.PeriodicGridDrawingStraightPortKeys
import LeanTrominoes.FiniteSeamCoordinates

/-! # Integral seam ports, including slope-controlled integer-column crossings

Vertical edges stay in the column strips. Every other row-seam crossing
gets an integral port inside its assigned slab, in its original order.
-/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

def seamCrossingCopies {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (line : Int) : List (Nat × Cell) :=
  (horizontalCrossingCopies graph drawing line).filter fun key => decide
    ((drawing.liftedStraightSegment key.1 key.2).start.1 ≠ (drawing.liftedStraightSegment key.1 key.2).finish.1)

def seamCrossingAbscissae {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (line : Int) : Finset ℚ :=
  ((seamCrossingCopies graph drawing line).map fun key => (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line).toFinset

def seamTowardLeft {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (line : Int) (abscissa : ℚ) : Bool :=
  (seamCrossingCopies graph drawing line).any fun key => decide
    ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line = abscissa ∧
      0 < (drawing.liftedStraightSegment key.1 key.2).rationalSlope)

def seamCrossingCoordinate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (abscissa : ℚ) : Int :=
  seamCoordinate (seamCrossingAbscissae graph drawing line) (seamTowardLeft graph drawing line)
    (crossingBound drawing.gridSize) abscissa

theorem seamCrossingAbscissae_card_bound {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) (line : Int) :
    (seamCrossingAbscissae graph drawing line).card ≤ crossingBound drawing.gridSize := by
  have subset : seamCrossingAbscissae graph drawing line ⊆ horizontalCrossingAbscissae graph drawing line := by
    intro abscissa member
    obtain ⟨key,keyMember,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨key,(List.mem_filter.mp keyMember).1,rfl⟩)
  exact (Finset.card_le_card subset).trans (horizontalCrossingAbscissae_card_bound compatible degree line)

theorem seamTowardLeft_at_key {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) (line : Int)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing line) :
    seamTowardLeft graph drawing line ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line) =
      decide (0 < (drawing.liftedStraightSegment key.1 key.2).rationalSlope) := by
  apply Bool.eq_iff_iff.mpr
  simp only [seamTowardLeft,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨other,otherMember,equal,positive⟩
    have same := horizontalCrossingCopies_abscissa_injective planar straight line
      (List.mem_filter.mp otherMember).1 (List.mem_filter.mp member).1 equal
    subst other
    exact positive
  · intro positive
    exact ⟨key,member,rfl,positive⟩

theorem seamCrossingSlab_integral {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2) (line column : Int)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing line)
    (integral : (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line = (column : ℚ)) :
    rationalSlab ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line)
      (seamTowardLeft graph drawing line ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa line)) =
      if 0 < (drawing.liftedStraightSegment key.1 key.2).rationalSlope then column-1 else column := by
  rw [seamTowardLeft_at_key planar straight line member,integral]
  simp [rationalSlab]

theorem seamCrossingCoordinates_strictMonoOn {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) (line : Int) :
    StrictMonoOn (seamCrossingCoordinate graph drawing line) (seamCrossingAbscissae graph drawing line) := by
  apply seamCoordinate_strictMonoOn
  exact_mod_cast seamCrossingAbscissae_card_bound compatible degree line

theorem seamCrossingCoordinate_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    (degree : graph.DegreeAtMost 4) {line : Int} {abscissa : ℚ} (member : abscissa ∈ seamCrossingAbscissae graph drawing line) :
    let column := rationalSlab abscissa (seamTowardLeft graph drawing line abscissa)
    (paddedRefinementFactor drawing.gridSize : Int)*column+7*crossingBound drawing.gridSize <
      seamCrossingCoordinate graph drawing line abscissa ∧
    seamCrossingCoordinate graph drawing line abscissa <
      (paddedRefinementFactor drawing.gridSize : Int)*(column+1)-7*crossingBound drawing.gridSize := by
  have countBound : ((seamCrossingAbscissae graph drawing line).card : Int) ≤ crossingBound drawing.gridSize := by
    exact_mod_cast seamCrossingAbscissae_card_bound compatible degree line
  have bounds := seamCoordinate_bounds (seamTowardLeft graph drawing line) member countBound
  dsimp only
  simp only [padded_vertexCoordinate_eq_factor] at bounds
  unfold seamCrossingCoordinate
  constructor <;> omega

end LeanTrominoes.PeriodicGridDrawing
