/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOrderedInheritedRouteSplicing

/-!
# Decomposing radially extended Figure 9 connectors

An extended clause-exit connector is its finite translated connector joined
to a two-point radial segment.  The pieces are exposed separately because
the radial segment can reverse the connector's final edge and is precisely
where finite loop erasure is required.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicOrthocrossing

namespace ComposedClauseExitFanData

/-- The radial half-edge attached to one finite exit connector. -/
def translatedRadialExtension
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (slot : Fin 3) : List Cell :=
  translatePolyline origin
    [sourceExit (data.direction slot),
      outerSourceExit (data.direction slot)]

/-- Translation preserves the defining connector/radial endpoint join. -/
theorem translatedExtendedRoute_eq_join
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (slot : Fin 3) :
    data.translatedExtendedRoute origin slot =
      joinAtEndpoint
        (data.translatedRoute origin slot)
        (data.translatedRadialExtension origin slot) := by
  simp [translatedExtendedRoute, translatedRoute,
    translatedRadialExtension, extendedRoute,
    translatePolyline, joinAtEndpoint, List.map_append]

/-- Every active finite exit connector is geometrically simple. -/
theorem route_isSimple :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        LocalIncidenceDrawing.RouteIsSimple (data.route slot) := by
  native_decide

/-- Pointwise translation preserves simplicity of an active connector. -/
theorem translatedRoute_isSimple
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot) :
    LocalIncidenceDrawing.RouteIsSimple
      (data.translatedRoute origin slot) := by
  unfold translatedRoute translatePolyline
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (data.route_isSimple valid slot active) origin

/-- Every active two-point radial extension is orthogonal. -/
theorem radialExtension_orthogonal :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        OrthogonalPolyline
          [sourceExit (data.direction slot),
            outerSourceExit (data.direction slot)] := by
  native_decide

/-- Every active two-point radial extension is geometrically simple. -/
theorem radialExtension_isSimple :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        LocalIncidenceDrawing.RouteIsSimple
          [sourceExit (data.direction slot),
            outerSourceExit (data.direction slot)] := by
  native_decide

/-- Translation preserves orthogonality of the radial extension. -/
theorem translatedRadialExtension_orthogonal
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot) :
    OrthogonalPolyline
      (data.translatedRadialExtension origin slot) := by
  exact (data.radialExtension_orthogonal valid slot active).translate origin

/-- Translation preserves simplicity of the radial extension. -/
theorem translatedRadialExtension_isSimple
    (origin : Cell)
    (data : ComposedClauseExitFanData)
    (valid : data.IsValid)
    (slot : Fin 3)
    (active : data.SlotActive slot) :
    LocalIncidenceDrawing.RouteIsSimple
      (data.translatedRadialExtension origin slot) := by
  unfold translatedRadialExtension translatePolyline
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (data.radialExtension_isSimple valid slot active) origin

end ComposedClauseExitFanData
end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
