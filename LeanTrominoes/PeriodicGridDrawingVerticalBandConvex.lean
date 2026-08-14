/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingVerticalBand

/-!
# Vertical convexity of the open drawing halo
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- The open vertical halo is convex along an axis-aligned segment. -/
theorem PositionInExpandedVerticalBand.of_segment_contains
    {drawing : PeriodicGridDrawing} {segment : GridSegment} {point : Cell}
    (startInside :
      drawing.PositionInExpandedVerticalBand segment.start)
    (finishInside :
      drawing.PositionInExpandedVerticalBand segment.finish)
    (contains : segment.Contains point) :
    drawing.PositionInExpandedVerticalBand point := by
  simp only [PositionInExpandedVerticalBand] at startInside finishInside ⊢
  rcases contains with
      ⟨_horizontal, sameVertical, _between⟩ |
      ⟨_vertical, _sameHorizontal, between⟩
  · rw [sameVertical]
    exact startInside
  · rcases between with forward | backward
    · exact
        ⟨startInside.1.trans_le forward.1,
          forward.2.trans_lt finishInside.2⟩
    · exact
        ⟨finishInside.1.trans_le backward.1,
          backward.2.trans_lt startInside.2⟩

end PeriodicGridDrawing
end LeanTrominoes
