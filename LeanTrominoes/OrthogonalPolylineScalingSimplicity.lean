/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints
import LeanTrominoes.PeriodicGridDrawingScaling

/-! # Simplicity under positive route scaling -/

namespace LeanTrominoes

/-- Positive uniform scaling preserves continuous geometric simplicity. -/
theorem LocalIncidenceDrawing.RouteIsSimple.scalePolyline
    {route : List Cell}
    {factor : Int}
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (factorPositive : 0 < factor) :
    LocalIncidenceDrawing.RouteIsSimple
      (scalePolyline factor route) := by
  let geometry :
      PlanarThreeSAT.GridDrawingMap (Cell.scale factor) :=
    { injective := Cell.scale_injective factorPositive.ne'
      isAxisAligned := fun {segment} aligned => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          (GridSegment.isAxisAligned_scale_iff
            factorPositive segment).mpr aligned
      interiorContains_iff := fun {segment point} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorContains_scale_iff
            factorPositive segment point
      interiorsMeet_iff := fun {first second} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorsMeet_scale_iff
            factorPositive first second }
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_mapPoints
      geometry simple

end LeanTrominoes
