/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Translation of canonical orthogonal detours

The canonical five-point Manhattan detour is equivariant under a common
translation of its two advertised endpoints.  Together with unit-subdivision
equivariance, this lets local finite connector calculations apply in every
periodic anchor gauge.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Translating both advertised endpoints translates every point of the
canonical orthogonal detour. -/
theorem orthogonalDetour_add_left
    (offset source target : Cell) :
    orthogonalDetour
        (Cell.add offset source) (Cell.add offset target) =
      (orthogonalDetour source target).map (Cell.add offset) := by
  rcases offset with ⟨offsetX, offsetY⟩
  rcases source with ⟨sourceX, sourceY⟩
  rcases target with ⟨targetX, targetY⟩
  simp [orthogonalDetour, freshDetourCoordinate,
    Cell.add, max_add_add_left]
  constructor <;> ring

end PositionedPeriodicCNF
end LeanTrominoes
