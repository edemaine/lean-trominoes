/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirectionData

/-! # Translation invariance of first polyline directions -/

namespace LeanTrominoes
namespace AxisDirection

@[simp] theorem polylineFirstDirection_translatePolyline_static
    (offset : Cell) (points : List Cell) :
    polylineFirstDirection
        (PeriodicOrthocrossing.translatePolyline offset points) =
      polylineFirstDirection points := by
  cases points with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          rcases offset with ⟨offsetX, offsetY⟩
          rcases first with ⟨firstX, firstY⟩
          rcases second with ⟨secondX, secondY⟩
          simp [PeriodicOrthocrossing.translatePolyline,
            polylineFirstDirection, between, Cell.add]

end AxisDirection
end LeanTrominoes
