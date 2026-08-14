/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandTemplatePoint

/-!
# Vertical-band bounds for Figure 2 normalization templates
-/

namespace LeanTrominoes

open DegreeThreeVertexNormalization
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- The finite Figure 2 route tables lie in the radius-three box around the
local center. -/
private theorem figureTwoRoute_withinCoordinateRadius
    (omitted : VertexSide) (port : CanonicalVertexPort) :
    ∀ point ∈ route omitted port,
      WithinCoordinateRadius 3 center point := by
  cases omitted <;> cases port <;> native_decide

/-- An anchored Figure 2 route at an old band point lies in the enlarged
open vertical halo. -/
theorem normalizationTemplateAt_route_inExpandedVerticalBand
    {drawing : PeriodicGridDrawing} {position : Cell}
    (positionInside :
      drawing.PositionInExpandedVerticalBand position)
    (omitted : VertexSide) (port : CanonicalVertexPort) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInExpandedVerticalBand
        (normalizationTemplateAt position (route omitted port)) := by
  intro point pointMember
  unfold normalizationTemplateAt translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localMember, rfl⟩
  exact withinThree_normalizeVertexPosition_inExpandedVerticalBand
    positionInside
    ((figureTwoRoute_withinCoordinateRadius
      omitted port localPoint localMember).translate
        (Cell.scale vertexNormalizationScale position))

end PeriodicThreeDM
end LeanTrominoes
