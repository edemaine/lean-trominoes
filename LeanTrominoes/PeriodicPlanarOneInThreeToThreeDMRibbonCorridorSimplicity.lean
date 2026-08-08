import LeanTrominoes.OrthogonalPolylineJoinSimplicity
import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.OrthogonalPolylineEndpointDirectionSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation

/-!
# Simplicity of assembled ribbon corridors

Consecutive ribbon tiles meet only at their intended half-edge boundary.
A tile strictly avoids every nonconsecutive later tile when the corresponding
source points do not repeat.  These two facts let geometric simplicity compose
inductively along every duplicate-free unit source route.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Genuine cardinal directions are determined by their unit step. -/
theorem AxisDirection.eq_of_genuine_step_eq
    {first second : AxisDirection}
    (firstGenuine : first.IsGenuine)
    (secondGenuine : second.IsGenuine)
    (stepsEqual : first.step = second.step) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.step]

/-- A genuine unit source step places its endpoints in adjacent ribbon
macrocells. -/
theorem ribbonMacrocellCentersAdjacent_of_unitAxisStep
    {first second : Cell}
    (unit : AxisDirection.IsUnitAxisStep first second) :
    RibbonMacrocellCentersAdjacent first second := by
  rcases unit with ⟨direction, genuine, equation⟩
  rw [equation]
  rcases first with ⟨firstX, firstY⟩
  cases direction <;>
    simp_all [RibbonMacrocellCentersAdjacent,
      RibbonMacrocellOffsetAdjacent, AxisDirection.IsGenuine,
      AxisDirection.step, Cell.add, Cell.sub]

/-- Two nonconsecutive legal source-route tiles strictly avoid each other
when neither endpoint of the first outgoing source edge is reused by the
second tile. -/
theorem nonconsecutiveSourceRibbonMacrocellRoutes_strictlyAvoidEachOther
    {firstPrevious firstCenter firstNext
      secondPrevious secondCenter secondNext : Cell}
    (firstCenterNeSecondCenter : firstCenter ≠ secondCenter)
    (firstCenterNeSecondNext : firstCenter ≠ secondNext)
    (firstNextNeSecondCenter : firstNext ≠ secondCenter)
    (firstIncomingUnit :
      AxisDirection.IsUnitAxisStep firstPrevious firstCenter)
    (firstOutgoingUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (secondIncomingUnit :
      AxisDirection.IsUnitAxisStep secondPrevious secondCenter)
    (secondOutgoingUnit :
      AxisDirection.IsUnitAxisStep secondCenter secondNext)
    (firstNoReverse :
      AxisDirection.between firstCenter firstNext ≠
        (AxisDirection.between firstPrevious firstCenter).opposite)
    (secondNoReverse :
      AxisDirection.between secondCenter secondNext ≠
        (AxisDirection.between secondPrevious secondCenter).opposite)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        (AxisDirection.between firstPrevious firstCenter)
        (AxisDirection.between firstCenter firstNext)
        firstColor)
      (ribbonMacrocellRoute secondCenter
        (AxisDirection.between secondPrevious secondCenter)
        (AxisDirection.between secondCenter secondNext)
        secondColor) := by
  have firstIncomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      firstIncomingUnit
  have firstOutgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      firstOutgoingUnit
  have secondIncomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondIncomingUnit
  have secondOutgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep
      secondOutgoingUnit
  apply ribbonMacrocellRoutes_strictlyAvoidEachOther_of_centers_ne
    firstCenterNeSecondCenter
    firstIncomingGenuine firstOutgoingGenuine firstNoReverse
    secondIncomingGenuine secondOutgoingGenuine secondNoReverse
    firstColor secondColor
  intro firstEnd secondEnd contact
  cases firstEnd <;> cases secondEnd
  · exact contact
  · rcases contact with
      ⟨offsetEq, sameOutgoing, _sameColor⟩
    have secondNextEquation :=
      AxisDirection.add_between_step_eq_of_unitAxisStep
        secondOutgoingUnit
    have secondCenterEquation :
        secondCenter =
          Cell.add firstCenter
            (AxisDirection.between
              firstPrevious firstCenter).opposite.step := by
      calc
        secondCenter = Cell.add firstCenter
            (Cell.sub secondCenter firstCenter) := by
          rcases firstCenter with ⟨firstX, firstY⟩
          rcases secondCenter with ⟨secondX, secondY⟩
          simp [Cell.add, Cell.sub]
        _ = Cell.add firstCenter
            (AxisDirection.between
              firstPrevious firstCenter).opposite.step := by
          rw [offsetEq]
    apply firstCenterNeSecondNext
    calc
      firstCenter =
          Cell.add
            (Cell.add firstCenter
              (AxisDirection.between
                firstPrevious firstCenter).opposite.step)
            (AxisDirection.between
              firstPrevious firstCenter).step := by
        exact
          (AxisDirection.add_opposite_step_add_step
            firstCenter firstIncomingGenuine).symm
      _ = Cell.add secondCenter
            (AxisDirection.between
              firstPrevious firstCenter).step := by
        rw [secondCenterEquation]
      _ = Cell.add secondCenter
            (AxisDirection.between
              secondCenter secondNext).step := by
        rw [sameOutgoing]
      _ = secondNext := secondNextEquation.symm
  · rcases contact with
      ⟨offsetEq, _sameIncoming, _sameColor⟩
    have firstNextEquation :=
      AxisDirection.add_between_step_eq_of_unitAxisStep
        firstOutgoingUnit
    apply firstNextNeSecondCenter
    calc
      firstNext = Cell.add firstCenter
          (AxisDirection.between firstCenter firstNext).step :=
        firstNextEquation
      _ = Cell.add firstCenter
          (Cell.sub secondCenter firstCenter) := by
        rw [offsetEq]
      _ = secondCenter := by
        rcases firstCenter with ⟨firstX, firstY⟩
        rcases secondCenter with ⟨secondX, secondY⟩
        simp [Cell.add, Cell.sub]
  · exact contact

/-- One legal tile strictly avoids a later corridor when both source points
of its outgoing edge are fresh among all later tile centers and successors. -/
theorem ribbonMacrocellRoute_strictlyAvoids_laterRibbonCorridorCore
    {firstPrevious firstCenter firstNext : Cell}
    (firstIncomingUnit :
      AxisDirection.IsUnitAxisStep firstPrevious firstCenter)
    (firstOutgoingUnit :
      AxisDirection.IsUnitAxisStep firstCenter firstNext)
    (firstNoReverse :
      AxisDirection.between firstCenter firstNext ≠
        (AxisDirection.between firstPrevious firstCenter).opposite)
    (secondPrevious secondCenter secondNext : Cell)
    (secondRest : List Cell)
    (secondUnitSteps :
      (secondPrevious :: secondCenter :: secondNext :: secondRest).IsChain
        AxisDirection.IsUnitAxisStep)
    (secondNoReversal :
      SourceRouteHasNoImmediateReversal
        (secondPrevious :: secondCenter :: secondNext :: secondRest))
    (firstCenterFresh :
      firstCenter ∉ secondCenter :: secondNext :: secondRest)
    (firstNextFresh :
      firstNext ∉ secondCenter :: secondNext :: secondRest)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        (AxisDirection.between firstPrevious firstCenter)
        (AxisDirection.between firstCenter firstNext)
        firstColor)
      (ribbonCorridorCore secondColor
        (secondPrevious :: secondCenter :: secondNext :: secondRest)) := by
  induction secondRest generalizing
      secondPrevious secondCenter secondNext with
  | nil =>
      rw [ribbonCorridorCore]
      have secondParts := unitSteps_cons_cons_cons secondUnitSteps
      have firstCenterParts :
          firstCenter ≠ secondCenter ∧
            firstCenter ≠ secondNext := by
        simpa using firstCenterFresh
      have firstNextParts :
          firstNext ≠ secondCenter ∧
            firstNext ≠ secondNext := by
        simpa using firstNextFresh
      exact
        nonconsecutiveSourceRibbonMacrocellRoutes_strictlyAvoidEachOther
          firstCenterParts.1 firstCenterParts.2 firstNextParts.1
          firstIncomingUnit firstOutgoingUnit
          secondParts.1 secondParts.2.1
          firstNoReverse secondNoReversal.1
          firstColor secondColor
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have secondParts := unitSteps_cons_cons_cons secondUnitSteps
      have firstCenterParts :
          firstCenter ≠ secondCenter ∧
            firstCenter ∉ secondNext :: fourth :: rest := by
        simpa using firstCenterFresh
      have firstNextParts :
          firstNext ≠ secondCenter ∧
            firstNext ∉ secondNext :: fourth :: rest := by
        simpa using firstNextFresh
      have firstCenterTailParts :
          firstCenter ≠ secondNext ∧
            firstCenter ∉ fourth :: rest := by
        simpa using firstCenterParts.2
      have headAvoid :=
        nonconsecutiveSourceRibbonMacrocellRoutes_strictlyAvoidEachOther
          firstCenterParts.1
          firstCenterTailParts.1
          firstNextParts.1
          firstIncomingUnit firstOutgoingUnit
          secondParts.1 secondParts.2.1
          firstNoReverse secondNoReversal.1
          firstColor secondColor
      have tailAvoid :=
        tailInduction secondCenter secondNext fourth
          secondParts.2.2 secondNoReversal.2
          firstCenterParts.2 firstNextParts.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          secondParts.2.1 secondColor
      apply headAvoid.join_right tailAvoid
        (ribbonMacrocellRoute_getLast? secondCenter
          (AxisDirection.between secondPrevious secondCenter)
          (AxisDirection.between secondCenter secondNext)
          secondColor)
      rw [shared]
      exact ribbonCorridorCore_head? secondColor
        secondCenter secondNext fourth rest

/-- Consecutive legal source-route tiles have no listed contact except their
intended shared half-edge boundary. -/
theorem consecutiveRibbonMacrocellRoutes_only_common
    {previous center next following : Cell}
    (incomingUnit :
      AxisDirection.IsUnitAxisStep previous center)
    (sharedUnit :
      AxisDirection.IsUnitAxisStep center next)
    (outgoingUnit :
      AxisDirection.IsUnitAxisStep next following)
    (firstNoReverse :
      AxisDirection.between center next ≠
        (AxisDirection.between previous center).opposite)
    (secondNoReverse :
      AxisDirection.between next following ≠
        (AxisDirection.between center next).opposite)
    (color : WireColor) :
    ∀ point,
      point ∈ ribbonMacrocellRoute center
        (AxisDirection.between previous center)
        (AxisDirection.between center next) color →
      point ∈ ribbonMacrocellRoute next
        (AxisDirection.between center next)
        (AxisDirection.between next following) color →
      point = ribbonMacrocellExit center
        (AxisDirection.between center next) color := by
  have incomingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep incomingUnit
  have sharedGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep sharedUnit
  have outgoingGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep outgoingUnit
  have centersDifferent : center ≠ next := sharedUnit.ne
  have centersAdjacent :
      RibbonMacrocellCentersAdjacent center next :=
    ribbonMacrocellCentersAdjacent_of_unitAxisStep sharedUnit
  have avoid :=
    ribbonMacrocellRoutes_avoidEachOther_of_centers_ne
      centersDifferent
      incomingGenuine sharedGenuine firstNoReverse
      sharedGenuine outgoingGenuine secondNoReverse color color
  intro point firstMember secondMember
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstEq⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondEq⟩
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex
      (firstEq.trans secondEq.symm)
  rw [firstEq, secondEq] at endpoints
  rcases
      (ribbonMacrocellRoutePointIsEndpoint_iff
        center
        (AxisDirection.between previous center)
        (AxisDirection.between center next)
        color point).mp endpoints.1 with
    firstEntry | firstExit
  · rcases
        (ribbonMacrocellRoutePointIsEndpoint_iff
          next
          (AxisDirection.between center next)
          (AxisDirection.between next following)
          color point).mp endpoints.2 with
      secondEntry | secondExit
    · have contact :=
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff
          centersAdjacent
          incomingGenuine sharedGenuine firstNoReverse
          sharedGenuine outgoingGenuine secondNoReverse
          color color .entry .entry).mp
          (firstEntry.symm.trans secondEntry)
      exact contact.elim
    · have contact :=
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff
          centersAdjacent
          incomingGenuine sharedGenuine firstNoReverse
          sharedGenuine outgoingGenuine secondNoReverse
          color color .entry .exit).mp
          (firstEntry.symm.trans secondExit)
      rcases contact with ⟨offsetEq, _sameDirection, _sameColor⟩
      have nextEquation :=
        AxisDirection.add_between_step_eq_of_unitAxisStep sharedUnit
      exact (firstNoReverse (by
        have stepsEqual :
            (AxisDirection.between center next).step =
              (AxisDirection.between previous center).opposite.step := by
          apply Cell.add_left_injective center
          calc
            Cell.add center
                (AxisDirection.between center next).step = next :=
              nextEquation.symm
            _ = Cell.add center (Cell.sub next center) := by
              rcases center with ⟨centerX, centerY⟩
              rcases next with ⟨nextX, nextY⟩
              simp [Cell.add, Cell.sub]
            _ = Cell.add center
                (AxisDirection.between previous center).opposite.step := by
              rw [offsetEq]
        exact AxisDirection.eq_of_genuine_step_eq
          sharedGenuine
          (AxisDirection.opposite_isGenuine incomingGenuine)
          stepsEqual)).elim
  · exact firstExit

/-- Every corridor assembled along a duplicate-free unit source route is a
geometrically simple polyline. -/
theorem ribbonCorridorCore_simple
    (color : WireColor)
    (first second : Cell)
    (rest : List Cell)
    (unitSteps :
      (first :: second :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (first :: second :: rest))
    (nodup : (first :: second :: rest).Nodup) :
    LocalIncidenceDrawing.RouteIsSimple
      (ribbonCorridorCore color (first :: second :: rest)) := by
  induction rest generalizing first second with
  | nil =>
      simp [LocalIncidenceDrawing.RouteIsSimple,
        gridPolylineSegments]
  | cons next rest tailInduction =>
      cases rest with
      | nil =>
          rw [ribbonCorridorCore]
          have parts := unitSteps_cons_cons_cons unitSteps
          exact ribbonMacrocellRoute_simple second
            (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
            (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
            noReversal.1 color
      | cons fourth rest =>
          rw [ribbonCorridorCore]
          have parts := unitSteps_cons_cons_cons unitSteps
          have tailParts := unitSteps_cons_cons_cons parts.2.2
          have headSimple :=
            ribbonMacrocellRoute_simple second
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
              noReversal.1 color
          have tailSimple :=
            tailInduction second next
              parts.2.2 noReversal.2 nodup.tail
          have tailHead :
              (ribbonCorridorCore color
                (second :: next :: fourth :: rest)).head? =
                some (ribbonMacrocellExit second
                  (AxisDirection.between second next) color) := by
            rw [ribbonMacrocellExit_eq_entry_of_unitAxisStep
              parts.2.1 color]
            exact ribbonCorridorCore_head? color
              second next fourth rest
          have headLast :=
            ribbonMacrocellRoute_getLast? second
              (AxisDirection.between first second)
              (AxisDirection.between second next) color
          have headTailAvoid :
              RoutesAvoidEachOther
                (ribbonMacrocellRoute second
                  (AxisDirection.between first second)
                  (AxisDirection.between second next) color)
                (ribbonCorridorCore color
                  (second :: next :: fourth :: rest)) := by
            cases rest with
            | nil =>
                rw [ribbonCorridorCore]
                exact ribbonMacrocellRoutes_avoidEachOther_of_centers_ne
                  (by
                    intro equal
                    exact parts.2.1.ne equal)
                  (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
                  (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
                  noReversal.1
                  (AxisDirection.between_isGenuine_of_unitAxisStep
                    parts.2.1)
                  (AxisDirection.between_isGenuine_of_unitAxisStep
                    tailParts.2.1)
                  noReversal.2.1 color color
            | cons fifth rest =>
                rw [ribbonCorridorCore]
                have immediateAvoid :=
                  ribbonMacrocellRoutes_avoidEachOther_of_centers_ne
                    (by
                      intro equal
                      exact parts.2.1.ne equal)
                    (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
                    (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
                    noReversal.1
                    (AxisDirection.between_isGenuine_of_unitAxisStep
                      parts.2.1)
                    (AxisDirection.between_isGenuine_of_unitAxisStep
                      tailParts.2.1)
                    noReversal.2.1 color color
                apply immediateAvoid.join_right_of_strict_suffix
                · apply ribbonMacrocellRoute_strictlyAvoids_laterRibbonCorridorCore
                    parts.1 parts.2.1 noReversal.1
                    next fourth fifth rest
                    tailParts.2.2
                    noReversal.2.2
                  · intro member
                    exact (List.nodup_cons.mp nodup.tail).1
                      (by simp [member])
                  · simpa using
                      (List.nodup_cons.mp
                        (List.nodup_cons.mp nodup.tail).2).1
                · exact ribbonMacrocellRoute_getLast? next
                    (AxisDirection.between second next)
                    (AxisDirection.between next fourth) color
                · rw [ribbonMacrocellExit_eq_entry_of_unitAxisStep
                      (show AxisDirection.IsUnitAxisStep next fourth from
                        tailParts.2.1) color]
                  exact ribbonCorridorCore_head? color
                    next fourth fifth rest
          apply headSimple.joinAtEndpoint_of_only_common
            tailSimple headTailAvoid headLast tailHead
          intro point headMember tailMember
          cases rest with
          | nil =>
              rw [ribbonCorridorCore] at tailMember
              exact consecutiveRibbonMacrocellRoutes_only_common
                parts.1 parts.2.1 tailParts.2.1
                noReversal.1 noReversal.2.1 color
                point headMember tailMember
          | cons fifth rest =>
              rw [ribbonCorridorCore] at tailMember
              rcases mem_joinAtEndpoint tailMember with
                immediateMember | laterMember
              · exact consecutiveRibbonMacrocellRoutes_only_common
                  parts.1 parts.2.1 tailParts.2.1
                  noReversal.1 noReversal.2.1 color
                  point headMember immediateMember
              ·
                have strict :=
                  ribbonMacrocellRoute_strictlyAvoids_laterRibbonCorridorCore
                    parts.1 parts.2.1 noReversal.1
                    next fourth fifth rest
                    tailParts.2.2
                    noReversal.2.2
                    (by
                      intro member
                      exact (List.nodup_cons.mp nodup.tail).1
                        (by simp [member]))
                    (by simpa using
                      (List.nodup_cons.mp
                        (List.nodup_cons.mp nodup.tail).2).1)
                    color color
                exact (strict.2.2.2 point headMember
                  point laterMember rfl).elim

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
