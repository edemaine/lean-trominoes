/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandMagnifiedRoute

/-!
# Vertical-band preservation under normalization-route splicing
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Splicing two band-contained local templates around the trimmed affine
image of a band-contained orthogonal route preserves the enlarged halo. -/
theorem normalizeRouteWithTemplates_inExpandedVerticalBand
    {drawing : PeriodicGridDrawing}
    {sourcePosition targetPosition : Cell}
    {sourceTemplate targetTemplate oldRoute : List Cell}
    (orthogonal : OrthogonalPolyline oldRoute)
    (oldInside : drawing.PolylineInExpandedVerticalBand oldRoute)
    (sourceInside :
      (vertexNormalizationMagnifiedUnitDrawing drawing)
        |>.PolylineInExpandedVerticalBand
          (normalizationTemplateAt sourcePosition sourceTemplate))
    (targetInside :
      (vertexNormalizationMagnifiedUnitDrawing drawing)
        |>.PolylineInExpandedVerticalBand
          (normalizationTemplateAt targetPosition targetTemplate)) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.PolylineInExpandedVerticalBand
        (normalizeRouteWithTemplates
          sourcePosition targetPosition
          sourceTemplate targetTemplate oldRoute) := by
  intro point pointMember
  unfold normalizeRouteWithTemplates at pointMember
  rcases mem_joinAtEndpoint pointMember with
    sourceMember | remainingMember
  · exact sourceInside point sourceMember
  · rcases mem_joinAtEndpoint remainingMember with
      trimmedMember | targetReverseMember
    · have magnifiedMember : point ∈ magnifiedUnitRoute oldRoute := by
        simp only [trimmedMagnifiedRoute] at trimmedMember
        exact List.mem_of_mem_drop
          (List.mem_of_mem_take trimmedMember)
      exact magnifiedUnitRoute_inExpandedVerticalBand
        orthogonal oldInside point magnifiedMember
    · exact targetInside point
        (List.mem_reverse.mp targetReverseMember)

end PeriodicThreeDM
end LeanTrominoes
