/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalHorizontalCrossing
import LeanTrominoes.Common.Geometry.GridSegmentStraightRayKeys
import LeanTrominoes.Graphs.Drawings.Grid.FiniteRationalSlabPerturbation

/-! # Shifted horizontal intersections realize the slope-biased seam choices -/
namespace LeanTrominoes.GridSegment
open OrthogonalDrawingRefinement

def rationalAbscissaAt (segment : GridSegment) (height : ℚ) : ℚ :=
  (segment.start.1 : ℚ)+(height-segment.start.2)*
    ((segment.finish.1 : ℚ)-segment.start.1)/((segment.finish.2 : ℚ)-segment.start.2)

def horizontalSeamVelocity (segment : GridSegment) : ℚ :=
  -((segment.finish.1 : ℚ)-segment.start.1)/((segment.finish.2 : ℚ)-segment.start.2)

theorem rationalAbscissaAt_int (segment : GridSegment) (line : Int) :
    segment.rationalAbscissaAt line = segment.rationalLineAbscissa line := rfl

theorem rationalAbscissaAt_sub (segment : GridSegment) (height epsilon : ℚ) :
    segment.rationalAbscissaAt (height-epsilon) =
      segment.rationalAbscissaAt height+epsilon*segment.horizontalSeamVelocity := by
  unfold rationalAbscissaAt horizontalSeamVelocity
  ring

theorem horizontalSeamVelocity_negative_iff (segment : GridSegment) :
    segment.horizontalSeamVelocity < 0 ↔ 0 < segment.rationalSlope := by
  simp only [horizontalSeamVelocity,neg_div,neg_lt_zero,rationalSlope,div_pos_iff]
  constructor
  · rintro (⟨first,second⟩ | ⟨first,second⟩)
    · exact Or.inl ⟨second,first⟩
    · exact Or.inr ⟨second,first⟩
  · rintro (⟨first,second⟩ | ⟨first,second⟩)
    · exact Or.inl ⟨second,first⟩
    · exact Or.inr ⟨second,first⟩

theorem shifted_horizontal_seam_slab {segment : GridSegment} {line : Int} {epsilon : ℚ}
    (positive : 0 < epsilon)
    (small : epsilon < rationalSlabMargin (segment.rationalLineAbscissa line) segment.horizontalSeamVelocity) :
    rationalSlab (segment.rationalAbscissaAt ((line : ℚ)-epsilon)) false =
      rationalSlab (segment.rationalLineAbscissa line) (decide (0 < segment.rationalSlope)) := by
  rw [rationalAbscissaAt_sub,rationalAbscissaAt_int]
  simpa only [horizontalSeamVelocity_negative_iff] using rationalSlab_perturbation positive small

theorem finite_shifted_horizontal_seam_slabs (segments : List GridSegment) (line : Int)
    {segment : GridSegment} (member : segment ∈ segments) :
    let values := segments.map fun other => (other.rationalLineAbscissa line,other.horizontalSeamVelocity)
    rationalSlab (segment.rationalAbscissaAt ((line : ℚ)-RationalPerturbation.slabPerturbation values)) false =
      rationalSlab (segment.rationalLineAbscissa line) (decide (0 < segment.rationalSlope)) := by
  dsimp only
  apply shifted_horizontal_seam_slab (RationalPerturbation.slabPerturbation_positive _)
  exact RationalPerturbation.slabPerturbation_lt_slabMargin (List.mem_map.mpr ⟨segment,member,rfl⟩)

end LeanTrominoes.GridSegment
