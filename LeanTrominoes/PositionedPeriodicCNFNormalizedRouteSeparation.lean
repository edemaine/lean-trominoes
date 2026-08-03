import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes

/-!
# Relative separation through clause-anchor normalization

A positioned route is stored after subtracting its clause anchor.  Comparing
two stored routes with a relative lattice translation is therefore equivalent
to comparing their displayed physical routes with the relative translation
adjusted by the difference of their two anchors.  This file records that
identity and transports ordinary and strict continuous separation through it.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Physical translation subtracted from every point when a clause route is
put into its canonical periodic gauge. -/
def clauseAnchorTranslation
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable) : Cell :=
  placement.translation (PeriodicCNF.clauseAnchor clause.literals)

/-- Offset between displayed physical routes corresponding to one relative
translation between their canonically gauged stored representatives. -/
def relativePhysicalRouteOffset
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (firstClause secondClause : PositionedPeriodicClause Variable)
    (relativeTranslate : Cell) : Cell :=
  Cell.add (placement.translation relativeTranslate)
    (Cell.sub
      (clauseAnchorTranslation placement firstClause)
      (clauseAnchorTranslation placement secondClause))

/-- Clause-anchor normalization is pointwise translation by the negative
physical anchor. -/
theorem normalizeIncidenceRoute_eq_translate
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (route : List Cell) :
    normalizeIncidenceRoute placement clause route =
      route.map
        (Cell.add
          (Cell.scale (-1)
            (clauseAnchorTranslation placement clause))) := by
  unfold normalizeIncidenceRoute clauseAnchorTranslation
  apply List.map_congr_left
  intro point pointMember
  apply Prod.ext <;>
    simp [Cell.sub, Cell.add, Cell.scale] <;>
    ring

/-- Translating a normalized second route by a relative lattice offset is
the same as first adjusting the displayed route by the two-anchor difference
and then applying the first route's normalization translation. -/
theorem normalizeIncidenceRoute_relative_eq
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (firstClause secondClause : PositionedPeriodicClause Variable)
    (secondRoute : List Cell)
    (relativeTranslate : Cell) :
    (normalizeIncidenceRoute placement secondClause secondRoute).map
        (Cell.add (placement.translation relativeTranslate)) =
      (secondRoute.map
          (Cell.add
            (relativePhysicalRouteOffset placement
              firstClause secondClause relativeTranslate))).map
        (Cell.add
          (Cell.scale (-1)
            (clauseAnchorTranslation placement firstClause))) := by
  rw [normalizeIncidenceRoute_eq_translate]
  simp only [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  apply Prod.ext <;>
    simp [relativePhysicalRouteOffset,
      clauseAnchorTranslation, Cell.sub, Cell.add, Cell.scale] <;>
    ring

/-- Ordinary separation of the appropriately shifted displayed routes gives
ordinary separation of their canonically gauged relative representatives. -/
theorem normalizeIncidenceRoutes_relative_avoidEachOther
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (firstClause secondClause : PositionedPeriodicClause Variable)
    (firstRoute secondRoute : List Cell)
    (relativeTranslate : Cell)
    (physicalAvoid :
      RoutesAvoidEachOther firstRoute
        (secondRoute.map
          (Cell.add
            (relativePhysicalRouteOffset placement
              firstClause secondClause relativeTranslate)))) :
    RoutesAvoidEachOther
      (normalizeIncidenceRoute placement firstClause firstRoute)
      ((normalizeIncidenceRoute placement secondClause secondRoute).map
        (Cell.add (placement.translation relativeTranslate))) := by
  let offset :=
    Cell.scale (-1)
      (clauseAnchorTranslation placement firstClause)
  have translated :=
    routesAvoidEachOther_translate physicalAvoid offset
  rw [normalizeIncidenceRoute_eq_translate,
    normalizeIncidenceRoute_relative_eq]
  exact translated

/-- Contact-free separation is transported through the same relative anchor
calculation. -/
theorem normalizeIncidenceRoutes_relative_strictlyAvoidEachOther
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (firstClause secondClause : PositionedPeriodicClause Variable)
    (firstRoute secondRoute : List Cell)
    (relativeTranslate : Cell)
    (physicalAvoid :
      RoutesStrictlyAvoidEachOther firstRoute
        (secondRoute.map
          (Cell.add
            (relativePhysicalRouteOffset placement
              firstClause secondClause relativeTranslate)))) :
    RoutesStrictlyAvoidEachOther
      (normalizeIncidenceRoute placement firstClause firstRoute)
      ((normalizeIncidenceRoute placement secondClause secondRoute).map
        (Cell.add (placement.translation relativeTranslate))) := by
  let offset :=
    Cell.scale (-1)
      (clauseAnchorTranslation placement firstClause)
  have translated := physicalAvoid.translatePolyline offset
  rw [normalizeIncidenceRoute_eq_translate,
    normalizeIncidenceRoute_relative_eq]
  exact translated

end PositionedPeriodicCNF
end LeanTrominoes
