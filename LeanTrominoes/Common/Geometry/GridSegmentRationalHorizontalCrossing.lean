/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentAxisSwap
import LeanTrominoes.Common.Geometry.GridSegmentRationalVerticalCrossing
import LeanTrominoes.Common.Geometry.GridSegmentRationalCrossingTranslation

/-! # Exact rational intersections with horizontal periodic row seams -/
namespace LeanTrominoes.GridSegment

def CrossesHorizontalLine (segment : GridSegment) (line : Int) : Prop :=
  segment.swapAxes.CrossesVerticalLine line

instance (segment : GridSegment) (line : Int) : Decidable (segment.CrossesHorizontalLine line) := by
  unfold CrossesHorizontalLine
  infer_instance

def rationalLineAbscissa (segment : GridSegment) (line : Int) : ℚ :=
  segment.swapAxes.rationalLineHeight line

theorem rationalLineAbscissa_realContains {segment : GridSegment} {line : Int}
    (crosses : segment.CrossesHorizontalLine line) :
    segment.RealContains ((segment.rationalLineAbscissa line : ℝ),(line : ℝ)) :=
  (realContains_swapAxes _ _).mp (rationalLineHeight_realContains crosses)

theorem rationalLineAbscissa_not_endpoint {segment : GridSegment} {line : Int}
    (crosses : segment.CrossesHorizontalLine line) :
    ((segment.rationalLineAbscissa line : ℝ),(line : ℝ)) ≠ ((segment.start.1 : ℝ),(segment.start.2 : ℝ)) ∧
      ((segment.rationalLineAbscissa line : ℝ),(line : ℝ)) ≠ ((segment.finish.1 : ℝ),(segment.finish.2 : ℝ)) := by
  have avoids := rationalLineHeight_not_endpoint crosses
  constructor
  · intro equal
    exact avoids.1 (congrArg Prod.swap equal)
  · intro equal
    exact avoids.2 (congrArg Prod.swap equal)

theorem crossesHorizontalLine_translate (segment : GridSegment) (offset : Cell) (line : Int) :
    (segment.translate offset).CrossesHorizontalLine (line+offset.2) ↔ segment.CrossesHorizontalLine line := by
  unfold CrossesHorizontalLine
  rw [swapAxes_translate]
  exact crossesVerticalLine_translate _ _ _

theorem rationalLineAbscissa_translate (segment : GridSegment) (offset : Cell) (line : Int) :
    (segment.translate offset).rationalLineAbscissa (line+offset.2) = segment.rationalLineAbscissa line+offset.1 := by
  unfold rationalLineAbscissa
  rw [swapAxes_translate]
  exact rationalLineHeight_translate _ _ _

end LeanTrominoes.GridSegment
