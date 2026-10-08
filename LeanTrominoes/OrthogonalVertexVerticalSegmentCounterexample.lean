/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalVertexAnchorTemplates

/-! # A vertical edge must follow its own fan before leaving a vertex rectangle

With one east incidence and one north incidence, the east connector crosses
the positive vertical axis at height seven. Keeping the north edge as a
straight vertical segment would therefore create an unwanted intersection.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement

theorem east_fan_meets_vertical_segment_interior :
    GridPolyline.RealContains (rectangleTemplate ⟨0,1,true,false⟩ 0) (0,7) ∧
      (GridSegment.mk (0,0) (0,20)).RealInteriorContains (0,7) := by
  constructor
  · refine ⟨⟨(-1,7),(5,7)⟩,?_,?_⟩
    · decide +kernel
    · refine ⟨(1/6 : ℝ),?_,?_,?_,?_⟩ <;> norm_num
  · refine ⟨(7/20 : ℝ),?_,?_,?_,?_⟩ <;> norm_num

end LeanTrominoes.OrthogonalDrawingRefinement
