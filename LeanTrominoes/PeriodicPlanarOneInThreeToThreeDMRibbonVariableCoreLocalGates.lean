import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans
import LeanTrominoes.OrthogonalPolylineStrictSeparation

/-!
# Variable-site cores versus coordinated ribbon gates

The finite variable-site drawing ends routed incidences at connector ports,
while the coordinated ribbon construction starts its local gates at those
same ports.  This module checks the exact interface between the two finite
tables.  Every site route and every active local gate have disjoint segment
interiors and mutually avoid the other route's segment interiors.  The
colored site route selected for a gate has the stronger endpoint-permitting
separation certificate: its only listed contact with the gate is their
advertised splice port.

These statements are independent of the outer fan direction.  They are
therefore checked over just the one-, two-, and three-module variable-site
configurations and then packaged for `VariableRibbonFanData`.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The two connector patterns whose current local-gate tables have complete
endpoint-aware separation from the whole variable-site core.  The fixed-red
and fixed-blue tables are clear in the false orientation; fixed-green still
requires the remaining annular clearance repair. -/
def VariableLocalGateTableEndpointClear
    (kind : VariableConnectorKind) (polarity : Bool) : Prop :=
  polarity = false ∧ kind ≠ .fixedGreen

instance (kind : VariableConnectorKind) (polarity : Bool) :
    Decidable (VariableLocalGateTableEndpointClear kind polarity) := by
  unfold VariableLocalGateTableEndpointClear
  infer_instance

/-- The three continuous-separation fields used by periodic continuous
planarity, without imposing any condition on listed point-to-point
contacts. -/
def RoutesAvoidInteriorContacts
    (first second : List Cell) : Prop :=
  SegmentInteriorsDisjoint first second ∧
    RoutePointsAvoidInteriors first second ∧
    RoutePointsAvoidInteriors second first

instance (first second : List Cell) :
    Decidable (RoutesAvoidInteriorContacts first second) := by
  unfold RoutesAvoidInteriorContacts
  infer_instance

/-- Ordinary endpoint-permitting route separation contains the three
interior-contact fields. -/
theorem RoutesAvoidEachOther.toRoutesAvoidInteriorContacts
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second) :
    RoutesAvoidInteriorContacts first second :=
  ⟨avoid.1, avoid.2.1, avoid.2.2.1⟩

/-- Contact-free route separation in particular excludes every kind of
interior contact. -/
theorem RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second) :
    RoutesAvoidInteriorContacts first second :=
  RoutesAvoidEachOther.toRoutesAvoidInteriorContacts
    strict.toRoutesAvoidEachOther

/-- Membership hypotheses imply the indexed interior-contact predicate. -/
theorem routesAvoidInteriorContacts_of_mem
    {first second : List Cell}
    (segmentsAvoid :
      ∀ firstSegment ∈ gridPolylineSegments first,
        ∀ secondSegment ∈ gridPolylineSegments second,
          ¬GridSegment.InteriorsMeet firstSegment secondSegment)
    (firstPointsAvoid :
      ∀ firstPoint ∈ first,
        ∀ secondSegment ∈ gridPolylineSegments second,
          ¬secondSegment.InteriorContains firstPoint)
    (secondPointsAvoid :
      ∀ secondPoint ∈ second,
        ∀ firstSegment ∈ gridPolylineSegments first,
          ¬firstSegment.InteriorContains secondPoint) :
    RoutesAvoidInteriorContacts first second := by
  unfold RoutesAvoidInteriorContacts
    SegmentInteriorsDisjoint RoutePointsAvoidInteriors
  exact
    ⟨fun firstIndex secondIndex =>
        segmentsAvoid _ (List.get_mem _ firstIndex)
          _ (List.get_mem _ secondIndex),
      fun firstPointIndex secondSegmentIndex =>
        firstPointsAvoid _ (List.get_mem _ firstPointIndex)
          _ (List.get_mem _ secondSegmentIndex),
      fun secondPointIndex firstSegmentIndex =>
        secondPointsAvoid _ (List.get_mem _ secondPointIndex)
          _ (List.get_mem _ firstSegmentIndex)⟩

/-- Interior-contact avoidance is symmetric. -/
theorem RoutesAvoidInteriorContacts.symm
    {first second : List Cell}
    (avoid : RoutesAvoidInteriorContacts first second) :
    RoutesAvoidInteriorContacts second first := by
  unfold RoutesAvoidInteriorContacts
    SegmentInteriorsDisjoint RoutePointsAvoidInteriors at avoid ⊢
  refine ⟨?_, avoid.2.2, avoid.2.1⟩
  intro secondIndex firstIndex interiorsMeet
  exact avoid.1 firstIndex secondIndex
    ((GridSegment.interiorsMeet_comm _ _).mpr interiorsMeet)

/-- Membership form of the segment-interior field. -/
theorem RoutesAvoidInteriorContacts.segmentsAvoid_of_mem
    {first second : List Cell}
    (avoid : RoutesAvoidInteriorContacts first second)
    (firstSegment : GridSegment)
    (firstMember : firstSegment ∈ gridPolylineSegments first)
    (secondSegment : GridSegment)
    (secondMember : secondSegment ∈ gridPolylineSegments second) :
    ¬GridSegment.InteriorsMeet firstSegment secondSegment := by
  rcases List.mem_iff_get.mp firstMember with ⟨firstIndex, rfl⟩
  rcases List.mem_iff_get.mp secondMember with ⟨secondIndex, rfl⟩
  exact avoid.1 firstIndex secondIndex

/-- Membership form of the first-point/second-interior field. -/
theorem RoutesAvoidInteriorContacts.firstPointsAvoid_of_mem
    {first second : List Cell}
    (avoid : RoutesAvoidInteriorContacts first second)
    (firstPoint : Cell) (firstMember : firstPoint ∈ first)
    (secondSegment : GridSegment)
    (secondMember : secondSegment ∈ gridPolylineSegments second) :
    ¬secondSegment.InteriorContains firstPoint := by
  rcases List.mem_iff_get.mp firstMember with ⟨firstIndex, rfl⟩
  rcases List.mem_iff_get.mp secondMember with ⟨secondIndex, rfl⟩
  exact avoid.2.1 firstIndex secondIndex

/-- Membership form of the second-point/first-interior field. -/
theorem RoutesAvoidInteriorContacts.secondPointsAvoid_of_mem
    {first second : List Cell}
    (avoid : RoutesAvoidInteriorContacts first second)
    (secondPoint : Cell) (secondMember : secondPoint ∈ second)
    (firstSegment : GridSegment)
    (firstMember : firstSegment ∈ gridPolylineSegments first) :
    ¬firstSegment.InteriorContains secondPoint := by
  exact avoid.symm.firstPointsAvoid_of_mem
    secondPoint secondMember firstSegment firstMember

/-- A point in the first segment's relative interior cannot lie anywhere
on the second segment.  If it were internal to the second segment, the two
segment interiors would meet; if it were an endpoint, it would be a listed
point of the second route in the first segment's interior. -/
theorem RoutesAvoidInteriorContacts.firstInterior_not_secondContains
    {first second : List Cell}
    (avoid : RoutesAvoidInteriorContacts first second)
    (firstSegment : GridSegment)
    (firstMember : firstSegment ∈ gridPolylineSegments first)
    (secondSegment : GridSegment)
    (secondMember : secondSegment ∈ gridPolylineSegments second)
    (point : Cell)
    (firstContains : firstSegment.InteriorContains point) :
    ¬secondSegment.Contains point := by
  intro secondContains
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        secondContains with
    secondInterior | secondEndpoint
  · exact
      (avoid.segmentsAvoid_of_mem
        firstSegment firstMember secondSegment secondMember)
        (GridSegment.interiorsMeet_of_interiorContains
          firstContains secondInterior)
  · have endpoints := gridPolylineSegments_endpoints_mem secondMember
    rcases secondEndpoint with atStart | atFinish
    · exact
        (avoid.secondPointsAvoid_of_mem
          secondSegment.start endpoints.1 firstSegment firstMember)
          (atStart ▸ firstContains)
    · exact
        (avoid.secondPointsAvoid_of_mem
          secondSegment.finish endpoints.2 firstSegment firstMember)
          (atFinish ▸ firstContains)

/-- Joining two pieces on the right preserves interior-contact avoidance
when the first route avoids both pieces.  Listed-point coincidences need no
extra side condition because this predicate deliberately ignores them. -/
theorem RoutesAvoidInteriorContacts.join_right
    {first second extra : List Cell} {boundary : Cell}
    (secondAvoid : RoutesAvoidInteriorContacts first second)
    (extraAvoid : RoutesAvoidInteriorContacts first extra)
    (secondLast : second.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesAvoidInteriorContacts first (joinAtEndpoint second extra) := by
  have joinedSegments :
      gridPolylineSegments (joinAtEndpoint second extra) =
        gridPolylineSegments second ++ gridPolylineSegments extra :=
    gridPolylineSegments_joinAtEndpoint secondLast extraHead
  apply routesAvoidInteriorContacts_of_mem
  · intro firstSegment firstMember joinedSegment joinedMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with secondMember | extraMember
    · exact secondAvoid.segmentsAvoid_of_mem
        firstSegment firstMember joinedSegment secondMember
    · exact extraAvoid.segmentsAvoid_of_mem
        firstSegment firstMember joinedSegment extraMember
  · intro firstPoint firstPointMember joinedSegment joinedMember
    rw [joinedSegments, List.mem_append] at joinedMember
    rcases joinedMember with secondMember | extraMember
    · exact secondAvoid.firstPointsAvoid_of_mem
        firstPoint firstPointMember joinedSegment secondMember
    · exact extraAvoid.firstPointsAvoid_of_mem
        firstPoint firstPointMember joinedSegment extraMember
  · intro joinedPoint joinedPointMember firstSegment firstMember
    rcases mem_joinAtEndpoint joinedPointMember with
      secondMember | extraMember
    · exact secondAvoid.secondPointsAvoid_of_mem
        joinedPoint secondMember firstSegment firstMember
    · exact extraAvoid.secondPointsAvoid_of_mem
        joinedPoint extraMember firstSegment firstMember

/-- Joining two pieces on the left preserves interior-contact avoidance. -/
theorem RoutesAvoidInteriorContacts.join_left
    {first extra second : List Cell} {boundary : Cell}
    (firstAvoid : RoutesAvoidInteriorContacts first second)
    (extraAvoid : RoutesAvoidInteriorContacts extra second)
    (firstLast : first.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesAvoidInteriorContacts (joinAtEndpoint first extra) second :=
  (firstAvoid.symm.join_right extraAvoid.symm firstLast extraHead).symm

/-- Common pointwise translation preserves interior-contact avoidance. -/
theorem RoutesAvoidInteriorContacts.translatePolyline
    {first second : List Cell}
    (avoid : RoutesAvoidInteriorContacts first second)
    (offset : Cell) :
    RoutesAvoidInteriorContacts
      (translatePolyline offset first)
      (translatePolyline offset second) := by
  apply routesAvoidInteriorContacts_of_mem
  · rw [gridPolylineSegments_translatePolyline,
      gridPolylineSegments_translatePolyline]
    intro firstSegment firstMember secondSegment secondMember
    rcases List.mem_map.mp firstMember with
      ⟨sourceFirst, sourceFirstMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨sourceSecond, sourceSecondMember, rfl⟩
    intro interiorsMeet
    apply avoid.segmentsAvoid_of_mem
      sourceFirst sourceFirstMember sourceSecond sourceSecondMember
    exact (GridSegment.interiorsMeet_translate_both_iff
      sourceFirst sourceSecond offset).mp interiorsMeet
  · rw [gridPolylineSegments_translatePolyline]
    intro firstPoint firstMember secondSegment secondMember
    unfold PeriodicOrthocrossing.translatePolyline at firstMember
    rcases List.mem_map.mp firstMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    rcases List.mem_map.mp secondMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    intro interiorContains
    apply avoid.firstPointsAvoid_of_mem
      sourcePoint sourcePointMember sourceSegment sourceSegmentMember
    exact (PeriodicGridDrawing.interiorContains_translate_iff
      sourceSegment offset sourcePoint).mp (by simpa
        [PeriodicOrthocrossing.translatePolyline,
        Cell.add, add_comm] using interiorContains)
  · rw [gridPolylineSegments_translatePolyline]
    intro secondPoint secondMember firstSegment firstMember
    unfold PeriodicOrthocrossing.translatePolyline at secondMember
    rcases List.mem_map.mp secondMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    rcases List.mem_map.mp firstMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    intro interiorContains
    apply avoid.secondPointsAvoid_of_mem
      sourcePoint sourcePointMember sourceSegment sourceSegmentMember
    exact (PeriodicGridDrawing.interiorContains_translate_iff
      sourceSegment offset sourcePoint).mp (by simpa
        [PeriodicOrthocrossing.translatePolyline,
        Cell.add, add_comm] using interiorContains)

/-- Every route in a complete one-, two-, or three-module variable site
avoids the continuous interiors of every active local gate, in both
directions. -/
theorem variableSiteRoute_avoids_standardVariableLocalGateRoute :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot),
      ∀ (_active : slot.index < countPred + 1)
        (triple : ActiveVariableSiteTriple (countPred + 1) kind)
        (routeColor gateColor : WireColor),
        RoutesAvoidInteriorContacts
          (translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing (countPred + 1) kind polarity).route
              triple routeColor))
          (standardVariableLocalGateRoute
            slot (kind slot) (polarity slot) gateColor) := by
  native_decide

/-- A finite variable-site route and a gate belonging to a different
occurrence module have complete endpoint-aware separation.  Thus all
non-endpoint listed contacts admitted by the preceding all-pairs theorem
are local to one occurrence module. -/
theorem variableSiteRoute_avoids_standardVariableLocalGateRoute_of_slot_ne :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot),
      ∀ (_active : slot.index < countPred + 1)
        (triple : ActiveVariableSiteTriple (countPred + 1) kind)
        (routeColor gateColor : WireColor),
        triple.1.slot ≠ slot →
          RoutesAvoidEachOther
            (translatePolyline standardThreeStrandLayout.variableOffset
              ((variableSiteDrawing (countPred + 1) kind polarity).route
                triple routeColor))
            (standardVariableLocalGateRoute
              slot (kind slot) (polarity slot) gateColor) := by
  native_decide

/-- In either endpoint-clear local table, every core route has full
endpoint-aware separation from every gate in the selected occurrence
module.  The certificate ranges over complete one-, two-, and three-module
sites, so it includes the closing variable-cycle route. -/
theorem
    variableSiteRoute_avoids_standardVariableLocalGateRoute_of_endpointClear :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot),
      ∀ (_active : slot.index < countPred + 1)
        (triple : ActiveVariableSiteTriple (countPred + 1) kind)
        (routeColor gateColor : WireColor),
        VariableLocalGateTableEndpointClear
            (kind slot) (polarity slot) →
          RoutesAvoidEachOther
            (translatePolyline standardThreeStrandLayout.variableOffset
              ((variableSiteDrawing (countPred + 1) kind polarity).route
                triple routeColor))
            (standardVariableLocalGateRoute
              slot (kind slot) (polarity slot) gateColor) := by
  native_decide

/-- The finite variable-site route selected for an active gate has
endpoint-permitting continuous separation from that gate. -/
theorem routedVariableSiteRoute_avoids_standardVariableLocalGateRoute :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot),
      ∀ (active : slot.index < countPred + 1),
        ∀ (gateColor : WireColor),
          RoutesAvoidEachOther
            (translatePolyline standardThreeStrandLayout.variableOffset
              ((variableSiteDrawing (countPred + 1) kind polarity).route
                ⟨(VariableRibbonFanData.routedTriple
                    ⟨countPred, kind, polarity, fun _ => .invalid⟩
                    slot gateColor),
                  VariableRibbonFanData.routedTriple_matches
                    ⟨countPred, kind, polarity, fun _ => .invalid⟩
                    slot active gateColor⟩
                gateColor))
            (standardVariableLocalGateRoute
              slot (kind slot) (polarity slot) gateColor) := by
  native_decide

namespace VariableRibbonFanData

/-- Data-packaged form of the complete core-to-gate interior-avoidance
interface. -/
theorem variableSiteRoute_avoids_localGateRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (triple : ActiveVariableSiteTriple data.count data.kind)
    (routeColor gateColor : WireColor) :
    RoutesAvoidInteriorContacts
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          triple routeColor))
      (standardVariableLocalGateRoute
        slot (data.kind slot) (data.polarity slot) gateColor) := by
  exact variableSiteRoute_avoids_standardVariableLocalGateRoute
    data.countPred data.kind data.polarity slot active
    triple routeColor gateColor

/-- Data-packaged endpoint-aware separation for a core route and a gate in
a different occurrence module. -/
theorem variableSiteRoute_avoids_localGateRoute_of_slot_ne
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (triple : ActiveVariableSiteTriple data.count data.kind)
    (routeColor gateColor : WireColor)
    (differentSlot : triple.1.slot ≠ slot) :
    RoutesAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          triple routeColor))
      (standardVariableLocalGateRoute
        slot (data.kind slot) (data.polarity slot) gateColor) := by
  exact variableSiteRoute_avoids_standardVariableLocalGateRoute_of_slot_ne
    data.countPred data.kind data.polarity slot active
    triple routeColor gateColor differentSlot

/-- Data-packaged endpoint-aware separation for either local connector table
whose complete finite certificate is clear. -/
theorem variableSiteRoute_avoids_localGateRoute_of_endpointClear
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (triple : ActiveVariableSiteTriple data.count data.kind)
    (routeColor gateColor : WireColor)
    (clear :
      VariableLocalGateTableEndpointClear
        (data.kind slot) (data.polarity slot)) :
    RoutesAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          triple routeColor))
      (standardVariableLocalGateRoute
        slot (data.kind slot) (data.polarity slot) gateColor) := by
  exact
    variableSiteRoute_avoids_standardVariableLocalGateRoute_of_endpointClear
      data.countPred data.kind data.polarity slot active
      triple routeColor gateColor clear

/-- Data-packaged form of the advertised core-to-gate splice interface. -/
theorem routedVariableSiteRoute_avoids_localGateRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (gateColor : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active gateColor) gateColor))
      (standardVariableLocalGateRoute
        slot (data.kind slot) (data.polarity slot) gateColor) := by
  exact routedVariableSiteRoute_avoids_standardVariableLocalGateRoute
    data.countPred data.kind data.polarity slot active
    gateColor

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
