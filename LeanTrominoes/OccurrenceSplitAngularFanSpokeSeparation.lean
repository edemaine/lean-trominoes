import LeanTrominoes.OccurrenceSplitAngularFanBoundary
import LeanTrominoes.OrthogonalPolylineBoundingBox
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularPorts
import LeanTrominoes.RetainedAngularFanPositionedRoutes

/-!
# Separation of positioned Figure 7 spokes

The eight copied source incidences in the fixed Figure 7 gadget use a
finite family of orthogonal spoke routes inside one `24 × 24` macrocell.
This module certifies that distinct valid slots give contact-free routes at
a common occurrence origin.  It also packages the complementary geometric
case: spokes whose translated macrocell rectangles are strictly separated.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned

/-- Every listed point of every local Figure 7 spoke lies in its advertised
`24 × 24` macrocell. -/
theorem spokeRoute_inClosedGridRectangle
    (port : Port) (point : Cell)
    (pointMember : point ∈ spokeRoute port) :
    InClosedGridRectangle (0, 0) (24, 24) point := by
  rcases point with ⟨pointX, pointY⟩
  cases port <;>
    simp_all [spokeRoute, InClosedGridRectangle] <;>
    omega

/-- Translating a local spoke translates its enclosing macrocell. -/
theorem spokeRoute_map_add_inClosedGridRectangle
    (origin : Cell) (port : Port) (point : Cell)
    (pointMember :
      point ∈ (spokeRoute port).map (Cell.add origin)) :
    InClosedGridRectangle
      origin (Cell.add origin (24, 24)) point := by
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBounded :=
    spokeRoute_inClosedGridRectangle
      port localPoint localPointMember
  rcases origin with ⟨originX, originY⟩
  rcases localPoint with ⟨pointX, pointY⟩
  simp only [InClosedGridRectangle, Cell.add]
    at localBounded ⊢
  omega

/-- Distinct valid angular slots select contact-free local Figure 7
spokes.  This is the finite planarity certificate specialized to precisely
the eight source-incidence routes used by the global construction. -/
theorem spokeRoutes_strictlyAvoid_of_indices_ne
    (first second : Nat)
    (firstLt : first < 8)
    (secondLt : second < 8)
    (indicesDifferent : first ≠ second) :
    RoutesStrictlyAvoidEachOther
      (spokeRoute (angularPortOfIndex first))
      (spokeRoute (angularPortOfIndex second)) := by
  interval_cases first <;>
    interval_cases second <;>
    simp_all [angularPortOfIndex] <;>
    native_decide

/-- The common translation origin of a positioned occurrence fan. -/
def angularFanOccurrenceOrigin
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (logicalOffset : Cell) : Cell :=
  Cell.add
    (macroOrigin sourcePlacement atom)
    ((placement sourcePlacement).translation logicalOffset)

/-- A positioned angular spoke is exactly its local Figure 7 spoke
translated by the occurrence origin. -/
theorem angularFanSpokeRouteAt_eq_map_add
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (logicalOffset : Cell)
    (index : Nat) :
    angularFanSpokeRouteAt
        sourcePlacement atom logicalOffset index =
      (spokeRoute (angularPortOfIndex index)).map
        (Cell.add
          (angularFanOccurrenceOrigin
            sourcePlacement atom logicalOffset)) := by
  unfold angularFanSpokeRouteAt angularFanSpokeRoute
    angularFanOccurrenceOrigin
  rw [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases macroOrigin sourcePlacement atom with
    ⟨originX, originY⟩
  rcases (placement sourcePlacement).translation logicalOffset with
    ⟨translationX, translationY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add]
  constructor <;> ring

/-- Distinct valid slots at the same occurrence origin remain
contact-free after positioning. -/
theorem angularFanSpokeRoutesAt_strictlyAvoid_of_sameOrigin
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstAtom secondAtom : Variable)
    (firstLogicalOffset secondLogicalOffset : Cell)
    (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < 8)
    (secondLt : secondIndex < 8)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (originsEqual :
      angularFanOccurrenceOrigin sourcePlacement
          firstAtom firstLogicalOffset =
        angularFanOccurrenceOrigin sourcePlacement
          secondAtom secondLogicalOffset) :
    RoutesStrictlyAvoidEachOther
      (angularFanSpokeRouteAt sourcePlacement
        firstAtom firstLogicalOffset firstIndex)
      (angularFanSpokeRouteAt sourcePlacement
        secondAtom secondLogicalOffset secondIndex) := by
  rw [angularFanSpokeRouteAt_eq_map_add,
    angularFanSpokeRouteAt_eq_map_add, originsEqual]
  exact
    (spokeRoutes_strictlyAvoid_of_indices_ne
      firstIndex secondIndex
      firstLt secondLt indicesDifferent).map_add
        (angularFanOccurrenceOrigin sourcePlacement
          secondAtom secondLogicalOffset)

/-- Spokes in occurrence macrocells separated by a strict coordinate gap
are contact-free, independently of their selected slots. -/
theorem angularFanSpokeRoutesAt_strictlyAvoid_of_originsSeparated
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (firstAtom secondAtom : Variable)
    (firstLogicalOffset secondLogicalOffset : Cell)
    (firstIndex secondIndex : Nat)
    (originsSeparated :
      ClosedGridRectanglesSeparated
        (angularFanOccurrenceOrigin sourcePlacement
          firstAtom firstLogicalOffset)
        (Cell.add
          (angularFanOccurrenceOrigin sourcePlacement
            firstAtom firstLogicalOffset)
          (24, 24))
        (angularFanOccurrenceOrigin sourcePlacement
          secondAtom secondLogicalOffset)
        (Cell.add
          (angularFanOccurrenceOrigin sourcePlacement
            secondAtom secondLogicalOffset)
          (24, 24))) :
    RoutesStrictlyAvoidEachOther
      (angularFanSpokeRouteAt sourcePlacement
        firstAtom firstLogicalOffset firstIndex)
      (angularFanSpokeRouteAt sourcePlacement
        secondAtom secondLogicalOffset secondIndex) := by
  rw [angularFanSpokeRouteAt_eq_map_add,
    angularFanSpokeRouteAt_eq_map_add]
  exact
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (fun point pointMember =>
        spokeRoute_map_add_inClosedGridRectangle
          (angularFanOccurrenceOrigin sourcePlacement
            firstAtom firstLogicalOffset)
          (angularPortOfIndex firstIndex)
          point pointMember)
      (fun point pointMember =>
        spokeRoute_map_add_inClosedGridRectangle
          (angularFanOccurrenceOrigin sourcePlacement
            secondAtom secondLogicalOffset)
          (angularPortOfIndex secondIndex)
          point pointMember)
      originsSeparated

end OccurrenceSplitRing
end LeanTrominoes
