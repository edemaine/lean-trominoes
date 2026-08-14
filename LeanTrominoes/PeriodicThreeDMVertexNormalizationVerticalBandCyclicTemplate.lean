/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandTemplatePoint

/-!
# Vertical-band bounds for cyclic normalization templates
-/

namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Every selected finite cyclic route table lies in the radius-three box
around the local center. -/
private theorem cyclicRoute_withinCoordinateRadius
    (active : Bool) (oldPort : CanonicalVertexPort) :
    ∀ point ∈ (rotationRoundPortAndRoute active oldPort).2,
      WithinCoordinateRadius 3 center point := by
  cases active <;> cases oldPort <;> native_decide

/-- An anchored selected cyclic-round route at an old band point lies in the
enlarged open vertical halo. -/
theorem normalizationTemplateAt_rotationRoundRoute_inExpandedVerticalBand
    {drawing : PeriodicGridDrawing} {position : Cell}
    (positionInside :
      drawing.PositionInExpandedVerticalBand position)
    (active : Bool) (oldPort : CanonicalVertexPort) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInExpandedVerticalBand
        (normalizationTemplateAt position
          (rotationRoundPortAndRoute active oldPort).2) := by
  intro point pointMember
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  exact withinThree_normalizeVertexPosition_inExpandedVerticalBand
    positionInside
    ((cyclicRoute_withinCoordinateRadius
      active oldPort localPoint localMember).translate
        (Cell.scale vertexNormalizationScale position))

end PeriodicThreeDM
end LeanTrominoes
