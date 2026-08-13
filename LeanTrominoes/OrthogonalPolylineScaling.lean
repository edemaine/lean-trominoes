/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingScaling
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Scaling orthogonal polylines

Positive integral refinement preserves axis alignment of every consecutive
segment of a polyline.  This route-level form complements the existing
whole-drawing scaling theorem and supports local route splices assembled
before their containing drawing is packaged.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Scaling every point of an orthogonal polyline by a positive natural
factor preserves orthogonality. -/
theorem OrthogonalPolyline.scalePolyline
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points)
    {factor : Nat}
    (factorPositive : 0 < factor) :
    OrthogonalPolyline (LeanTrominoes.scalePolyline factor points) := by
  unfold OrthogonalPolyline at orthogonal ⊢
  unfold LeanTrominoes.scalePolyline
  apply List.isChain_map_of_isChain
    (Cell.scale factor)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_scale_iff
        (by exact_mod_cast factorPositive)
        (GridSegment.mk first second)).mpr aligned
  · exact orthogonal

end PeriodicOrthocrossing
end LeanTrominoes
