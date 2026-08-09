import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.PeriodicGridDrawingLiftedRouteSeparation
import LeanTrominoes.PositionedPeriodicCNFRibbonScaling

/-!
# Lifted ribbon separation under positive scaling

Positive uniform refinement preserves both complete separation of periodic
route occurrences and route-local simplicity.  These facts complement the
listed-point contact theorem in `PositionedPeriodicCNFRibbonScaling`.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Complete separation of every pair of lifted route occurrences survives
positive uniform scaling of a periodic drawing. -/
theorem liftedRoutesAvoidEachOther_scale
    {factor : Nat} (positive : 0 < factor)
    (drawing : PeriodicGridDrawing)
    (separated : drawing.LiftedRoutesAvoidEachOther) :
    (drawing.scale factor).LiftedRoutesAvoidEachOther := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate occurrencesDifferent
  rw [PeriodicGridDrawing.scale, List.zipIdx_map]
      at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstSource, firstSourceMember, firstEqual⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSource, secondSourceMember, secondEqual⟩
  have firstRouteEqual :
      first.1 = scalePolyline factor firstSource.1 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.fst firstEqual).symm
  have firstIndexEqual : first.2 = firstSource.2 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.snd firstEqual).symm
  have secondRouteEqual :
      second.1 = scalePolyline factor secondSource.1 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.fst secondEqual).symm
  have secondIndexEqual : second.2 = secondSource.2 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.snd secondEqual).symm
  have sourceOccurrencesDifferent :
      (firstSource.2, firstTranslate) ≠
        (secondSource.2, secondTranslate) := by
    intro equal
    have sourceIndexEqual : firstSource.2 = secondSource.2 :=
      congrArg (fun occurrence : Nat × Cell => occurrence.1) equal
    have translateEqual : firstTranslate = secondTranslate :=
      congrArg (fun occurrence : Nat × Cell => occurrence.2) equal
    apply occurrencesDifferent
    apply Prod.ext
    · exact firstIndexEqual.trans
        (sourceIndexEqual.trans secondIndexEqual.symm)
    · exact translateEqual
  have sourceAvoids := separated firstSource firstSourceMember
    secondSource secondSourceMember firstTranslate secondTranslate
    sourceOccurrencesDifferent
  have scaledAvoids :=
    sourceAvoids.scalePolyline (factor := (factor : Int))
      (by exact_mod_cast positive)
  rw [firstRouteEqual, secondRouteEqual]
  simpa [scalePolyline, List.map_map, Function.comp_def,
    periodTranslation_scale positive, Cell.scale_add] using scaledAvoids

/-- Positive uniform scaling preserves route-local simplicity throughout a
periodic route family. -/
theorem routesSimple_scale
    {factor : Nat} (positive : 0 < factor)
    (drawing : PeriodicGridDrawing)
    (simple : ∀ route ∈ drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈ (drawing.scale factor).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  let geometry :
      PlanarThreeSAT.GridDrawingMap (Cell.scale factor) :=
    { injective := Cell.scale_injective (by exact_mod_cast positive.ne')
      isAxisAligned := fun {segment} aligned => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          (GridSegment.isAxisAligned_scale_iff
            (by exact_mod_cast positive : (0 : Int) < factor) segment).mpr
              aligned
      interiorContains_iff := fun {segment point} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorContains_scale_iff
            (by exact_mod_cast positive : (0 : Int) < factor)
              segment point
      interiorsMeet_iff := fun {first second} => by
        simpa [GridSegment.mapPoints, GridSegment.scale] using
          GridSegment.interiorsMeet_scale_iff
            (by exact_mod_cast positive : (0 : Int) < factor)
              first second }
  intro scaledRoute scaledMember
  rw [PeriodicGridDrawing.scale] at scaledMember
  rcases List.mem_map.mp scaledMember with
    ⟨route, routeMember, rfl⟩
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_mapPoints
      geometry (simple route routeMember)

end PeriodicGridDrawing
end LeanTrominoes
