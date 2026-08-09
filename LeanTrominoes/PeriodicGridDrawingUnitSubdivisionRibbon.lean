import LeanTrominoes.OrthogonalPolylineLoopErasureSeparation
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
import LeanTrominoes.PeriodicGridDrawingLiftedRouteSeparation

/-!
# Ribbon separation through unit subdivision

Ordered unit subdivision does not change the geometric support of a simple
orthogonal route.  This file packages that observation at the level of
complete lifted route separation and endpoint-only contacts in a periodic
grid drawing.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Complete separation of two simple orthogonal routes survives ordered
unit subdivision. -/
theorem RoutesAvoidEachOther.unitSubdividePolyline
    {first second : List Cell}
    (avoids : RoutesAvoidEachOther first second)
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (firstSimple : LocalIncidenceDrawing.RouteIsSimple first)
    (secondSimple : LocalIncidenceDrawing.RouteIsSimple second) :
    RoutesAvoidEachOther
      (AxisDirection.unitSubdividePolyline first)
      (AxisDirection.unitSubdividePolyline second) := by
  rw [← AxisDirection.normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
      firstNonempty firstOrthogonal firstSimple,
    ← AxisDirection.normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
      secondNonempty secondOrthogonal secondSimple]
  exact avoids.normalizeOrthogonalPolyline
    firstNonempty secondNonempty firstOrthogonal secondOrthogonal

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicGridDrawing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Pairwise separation of complete lifted routes survives ordered unit
subdivision of every stored route. -/
theorem liftedRoutesAvoidEachOther_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (separated : drawing.LiftedRoutesAvoidEachOther)
    (orthogonal : drawing.IsOrthogonal)
    (nonempty : ∀ route ∈ drawing.edgeRoutes, route ≠ [])
    (simple : ∀ route ∈ drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route) :
    drawing.unitSubdivide.LiftedRoutesAvoidEachOther := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate occurrencesDifferent
  rw [unitSubdivide, List.zipIdx_map] at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstSource, firstSourceMember, firstEqual⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondSource, secondSourceMember, secondEqual⟩
  have firstRouteEqual :
      first.1 = AxisDirection.unitSubdividePolyline firstSource.1 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.fst firstEqual).symm
  have firstIndexEqual : first.2 = firstSource.2 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.snd firstEqual).symm
  have secondRouteEqual :
      second.1 = AxisDirection.unitSubdividePolyline secondSource.1 := by
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
  have sourceAvoids :=
    separated firstSource firstSourceMember
      secondSource secondSourceMember
      firstTranslate secondTranslate sourceOccurrencesDifferent
  have firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline firstSource.1 :=
    (isOrthogonal_iff_routes drawing).mp orthogonal
      firstSource.1 (List.fst_mem_of_mem_zipIdx firstSourceMember)
  have secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline secondSource.1 :=
    (isOrthogonal_iff_routes drawing).mp orthogonal
      secondSource.1 (List.fst_mem_of_mem_zipIdx secondSourceMember)
  have firstNonempty := nonempty firstSource.1
    (List.fst_mem_of_mem_zipIdx firstSourceMember)
  have secondNonempty := nonempty secondSource.1
    (List.fst_mem_of_mem_zipIdx secondSourceMember)
  have firstSimple := simple firstSource.1
    (List.fst_mem_of_mem_zipIdx firstSourceMember)
  have secondSimple := simple secondSource.1
    (List.fst_mem_of_mem_zipIdx secondSourceMember)
  have subdividedAvoids :=
    sourceAvoids.unitSubdividePolyline
      (by simpa using firstNonempty)
      (by simpa using secondNonempty)
      (firstOrthogonal.translate
        (drawing.periodTranslation firstTranslate))
      (secondOrthogonal.translate
        (drawing.periodTranslation secondTranslate))
      (routeIsSimple_translate firstSimple
        (drawing.periodTranslation firstTranslate))
      (routeIsSimple_translate secondSimple
        (drawing.periodTranslation secondTranslate))
  rw [firstRouteEqual, secondRouteEqual]
  simpa only [AxisDirection.unitSubdividePolyline_map_add,
    unitSubdivide_periodTranslation] using
    subdividedAvoids

/-- Ordered unit subdivision preserves route-local simplicity for every
stored simple orthogonal nonempty route. -/
theorem routesSimple_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal)
    (nonempty : ∀ route ∈ drawing.edgeRoutes, route ≠ [])
    (simple : ∀ route ∈ drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route) :
    ∀ route ∈ drawing.unitSubdivide.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro route routeMember
  rw [unitSubdivide] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨sourceRoute, sourceMember, rfl⟩
  have sourceOrthogonal :=
    (isOrthogonal_iff_routes drawing).mp orthogonal
      sourceRoute sourceMember
  have sourceNonempty := nonempty sourceRoute sourceMember
  rw [← AxisDirection.normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
      sourceNonempty sourceOrthogonal (simple sourceRoute sourceMember)]
  exact AxisDirection.normalizeOrthogonalPolyline_isSimple
    sourceNonempty sourceOrthogonal

/-- Endpoint-only listed-point contacts survive ordered unit subdivision of
a separated family of simple orthogonal nonempty routes. -/
theorem routePointsMeetOnlyAtEndpoints_unitSubdivide
    (drawing : PeriodicGridDrawing)
    (separated : drawing.LiftedRoutesAvoidEachOther)
    (orthogonal : drawing.IsOrthogonal)
    (nonempty : ∀ route ∈ drawing.edgeRoutes, route ≠ [])
    (simple : ∀ route ∈ drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route) :
    drawing.unitSubdivide.RoutePointsMeetOnlyAtEndpoints := by
  exact routePointsMeetOnlyAtEndpoints_of_liftedRoutesAvoidEachOther
    (liftedRoutesAvoidEachOther_unitSubdivide drawing separated
      orthogonal nonempty simple)
    (routesSimple_unitSubdivide drawing orthogonal nonempty simple)

end PeriodicGridDrawing
end LeanTrominoes
