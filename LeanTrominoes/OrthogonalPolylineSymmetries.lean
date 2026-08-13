/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Symmetries of orthogonal polylines

Translation and reversal preserve rectilinearity.  These elementary facts
are shared by route splicing and 3DM contraction, so they live here rather
than in either downstream construction.
-/

namespace LeanTrominoes

/-- Axis alignment is unchanged when the endpoints of a segment are
swapped. -/
theorem GridSegment.isAxisAligned_swap (first second : Cell) :
    (GridSegment.mk first second).IsAxisAligned ↔
      (GridSegment.mk second first).IsAxisAligned := by
  constructor
  · rintro (⟨same, different⟩ | ⟨same, different⟩)
    · exact Or.inl ⟨same.symm, different.symm⟩
    · exact Or.inr ⟨same.symm, different.symm⟩
  · rintro (⟨same, different⟩ | ⟨same, different⟩)
    · exact Or.inl ⟨same.symm, different.symm⟩
    · exact Or.inr ⟨same.symm, different.symm⟩

/-- Translating every point preserves orthogonality of a polyline. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.translate
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points)
    (offset : Cell) :
    OrthogonalPolyline (translatePolyline offset points) := by
  unfold OrthogonalPolyline translatePolyline
  apply List.isChain_map_of_isChain
    (Cell.add offset)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_translate
        (GridSegment.mk first second) offset).2 aligned
  · exact orthogonal

/-- Traversing an orthogonal polyline backward preserves orthogonality. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.reverse
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points) :
    OrthogonalPolyline points.reverse := by
  unfold OrthogonalPolyline at orthogonal ⊢
  rw [List.isChain_reverse]
  exact orthogonal.imp fun first second aligned =>
    (GridSegment.isAxisAligned_swap first second).mp aligned

end LeanTrominoes
