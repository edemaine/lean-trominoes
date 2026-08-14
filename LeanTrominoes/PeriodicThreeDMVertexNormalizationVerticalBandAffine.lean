/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandMagnifiedRoute

/-!
# Vertical-band bounds for affine vertex normalization

The common first half of every degree-three normalization round magnifies by
twelve, subdivides into unit steps, and translates by the local-template
center `(3, 3)`.
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The complete affine/unit-refinement stage preserves the open vertical
halo route by route. -/
theorem vertexNormalizationMagnifiedUnitDrawing_routePointsInExpandedVerticalBand
    {drawing : PeriodicGridDrawing}
    (orthogonal : drawing.IsOrthogonal)
    (inside : drawing.RoutePointsInExpandedVerticalBand) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.RoutePointsInExpandedVerticalBand := by
  intro route routeMember point pointMember
  rw [vertexNormalizationMagnifiedUnitDrawing_edgeRoutes] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨sourceRoute, sourceRouteMember, rfl⟩
  have sourceOrthogonal :=
    (PeriodicGridDrawing.isOrthogonal_iff_routes drawing).mp orthogonal
      sourceRoute sourceRouteMember
  exact magnifiedUnitRoute_inExpandedVerticalBand sourceOrthogonal
    (fun source sourceMember =>
      inside sourceRoute sourceRouteMember source sourceMember)
    point pointMember

end PeriodicThreeDM
end LeanTrominoes
