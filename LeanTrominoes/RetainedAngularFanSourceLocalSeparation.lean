import LeanTrominoes.RetainedAngularFanOuterLocalRoutes
import LeanTrominoes.RetainedAngularFanSourceScaling
import LeanTrominoes.ScaledPointNeighborhoodSeparation

/-!
# Separating a refined source prefix from a local outer fan

The local part of every outer fan stays in the fixed radius-288 square
around its variable center.  After any source-first refinement by a factor
greater than one, the combined source scale is strictly larger than that
radius.  The generic lattice-clearance theorem therefore separates a
source prefix from this complete local route as soon as the unscaled prefix
avoids the other variable center.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Successive natural scale factors on a polyline multiply. -/
@[simp]
theorem scalePolyline_scalePolyline_nat
    (first second : Nat) (points : List Cell) :
    scalePolyline first (scalePolyline second points) =
      scalePolyline (first * second) points := by
  induction points with
  | nil =>
      rfl
  | cons point points _ =>
      simp [scalePolyline, Cell.scale_scale]

/-- Positioning a local outer-fan route preserves its radius-288 bound. -/
theorem retainedTerminalFanOuterLocalRouteAt_points_within_outer_frame
    (center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        retainedTerminalFanOuterLocalRouteAt
          center direction slot) :
    WithinCoordinateRadius 288 center point := by
  rw [retainedTerminalFanOuterLocalRouteAt,
    List.mem_map] at pointMember
  rcases pointMember with
    ⟨offset, offsetMember, rfl⟩
  have bounded :=
    retainedTerminalFanOuterLocalRoute_points_within_outer_frame
      direction slot offset offsetMember
  have translated := bounded.translate center
  simpa [Cell.add] using translated

/-- A twice-or-more refined source prefix strictly avoids the complete
local radius-288 part of another outer fan, provided the unscaled prefix
does not contain that fan's center. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerLocalRoute
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (sourceRoute : List Cell)
    (otherCenter : Cell)
    (otherDirection : RetainedTerminalDirection)
    (otherSlot : RetainedTerminalSlot)
    (sourcePointsAvoid :
      ∀ point ∈ sourceRoute.dropLast,
        point ≠ otherCenter)
    (sourceSegmentsAvoid :
      ∀ segment ∈
          gridPolylineSegments sourceRoute.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains otherCenter) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterLocalRouteAt
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale factor otherCenter))
        otherDirection otherSlot) := by
  let combinedFactor :=
    retainedTerminalFanTotalRefinement * factor
  have combinedPositive : 0 < combinedFactor := by
    dsimp [combinedFactor]
    exact Nat.mul_pos
      (by native_decide) (by omega)
  have radiusLt : 288 < combinedFactor := by
    dsimp [combinedFactor]
    rw [retainedTerminalFanTotalRefinement_eq]
    omega
  have separated :=
    routesStrictlyAvoidEachOther_scalePolyline_pointNeighborhood
      (source := sourceRoute.dropLast)
      (nearby :=
        retainedTerminalFanOuterLocalRouteAt
          (Cell.scale combinedFactor otherCenter)
          otherDirection otherSlot)
      combinedPositive radiusLt
      sourcePointsAvoid sourceSegmentsAvoid
      (fun point pointMember =>
        retainedTerminalFanOuterLocalRouteAt_points_within_outer_frame
          (Cell.scale combinedFactor otherCenter)
          otherDirection otherSlot pointMember)
  simpa [combinedFactor, scalePolyline,
    List.map_map, Function.comp_def,
    Cell.scale_scale, Nat.cast_mul] using separated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
