/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingShiftedSeamGeometry
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalSlabPerturbationBounds

/-! # Shifted seam crossings lie strictly inside their assigned slabs -/
namespace LeanTrominoes
namespace GridSegment

theorem horizontalSeamVelocity_ne_zero {segment : GridSegment} {line : Int}
    (crosses : segment.CrossesHorizontalLine line) (nonvertical : segment.start.1 ≠ segment.finish.1) :
    segment.horizontalSeamVelocity ≠ 0 := by
  have differentY : segment.finish.2 ≠ segment.start.2 := by
    change (segment.start.2 < line ∧ line < segment.finish.2) ∨
      (segment.finish.2 < line ∧ line < segment.start.2) at crosses
    rcases crosses with forward | backward <;> omega
  unfold horizontalSeamVelocity
  exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast nonvertical.symm)))
    (sub_ne_zero.mpr (by exact_mod_cast differentY))

end GridSegment
namespace PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem shiftedSeamAbscissa_strict_slab_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) :
    let column := rationalSlab ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)
      (seamTowardLeft graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0))
    (column : ℚ) < shiftedSeamAbscissa graph drawing key ∧ shiftedSeamAbscissa graph drawing key < (column : ℚ)+1 := by
  have horizontalMember := (List.mem_filter.mp member).1
  have crosses := (of_decide_eq_true (List.mem_filter.mp horizontalMember).2).1
  have nonvertical := of_decide_eq_true (List.mem_filter.mp member).2
  have nonzero := GridSegment.horizontalSeamVelocity_ne_zero crosses nonvertical
  have bounds := rationalSlab_perturbation_strict_bounds (seamPerturbation_positive graph drawing)
    (RationalPerturbation.slabPerturbation_lt_slabMargin (mem_seamPerturbationValues member)) nonzero
  dsimp only
  rw [seamTowardLeft_at_key planar straight 0 member,shiftedSeamAbscissa_eq_evaluate]
  simpa only [GridSegment.horizontalSeamVelocity_negative_iff,RationalPerturbation.evaluate] using bounds

theorem shiftedSeamAbscissa_in_cell {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) :
    0 < shiftedSeamAbscissa graph drawing key ∧ shiftedSeamAbscissa graph drawing key < (drawing.gridSize : ℚ) := by
  have coordMember : (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0 ∈ seamCrossingAbscissae graph drawing 0 :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨key,member,rfl⟩)
  have oldBounds := seamCrossingAbscissae_interior planar.1.1 graphLocal straight coordMember
  have slabBounds := rationalSlab_in_fundamental (period := drawing.gridSize) oldBounds
    (seamTowardLeft graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0))
  have bounds := shiftedSeamAbscissa_strict_slab_bounds planar straight member
  dsimp only at bounds
  have lower : (0 : ℚ) ≤ rationalSlab ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)
      (seamTowardLeft graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)) := by exact_mod_cast slabBounds.1
  have upper : (rationalSlab ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)
      (seamTowardLeft graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)) : ℚ)+1 ≤ drawing.gridSize := by
    exact_mod_cast (by omega : rationalSlab ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0)
      (seamTowardLeft graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0))+1 ≤ drawing.gridSize)
  exact ⟨lt_of_le_of_lt lower bounds.1,lt_of_lt_of_le bounds.2 upper⟩

end PeriodicGridDrawing
end LeanTrominoes
