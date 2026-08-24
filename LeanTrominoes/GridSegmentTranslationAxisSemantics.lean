/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawing

/-! # Translation invariance of grid-segment axes -/

namespace LeanTrominoes.GridSegment

@[simp] theorem translate_isHorizontal_iff
    (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).IsHorizontal ↔ segment.IsHorizontal := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [translate, IsHorizontal, Cell.add]

@[simp] theorem translate_isVertical_iff
    (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).IsVertical ↔ segment.IsVertical := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [translate, IsVertical, Cell.add]

end LeanTrominoes.GridSegment
