import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorAssembly
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation

/-!
# Separation of assembled ribbon corridors

Different ribbon colors must remain disjoint after their macrocell pieces
are joined into complete corridor cores.  The key recursive lemma separates
one legal tile from every later tile of a corridor when its center does not
reappear.  A duplicate-free source route supplies exactly that condition.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- One legal macrocell route is contact-free from a differently colored
later corridor whenever its center does not occur among that corridor's
tile centers. -/
theorem ribbonMacrocellRoute_strictlyAvoids_ribbonCorridorCore
    {sourceCenter : Cell}
    {sourceIncoming sourceOutgoing : AxisDirection}
    (sourceIncomingGenuine : sourceIncoming.IsGenuine)
    (sourceOutgoingGenuine : sourceOutgoing.IsGenuine)
    (sourceNoReverse :
      sourceOutgoing ≠ sourceIncoming.opposite)
    {sourceColor corridorColor : WireColor}
    (colorsDifferent : sourceColor ≠ corridorColor)
    (first center next : Cell) (rest : List Cell)
    (unitSteps :
      (first :: center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (first :: center :: next :: rest))
    (sourceCenterFresh :
      sourceCenter ∉ center :: next :: rest) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute sourceCenter
        sourceIncoming sourceOutgoing sourceColor)
      (ribbonCorridorCore corridorColor
        (first :: center :: next :: rest)) := by
  induction rest generalizing first center next with
  | nil =>
      rw [ribbonCorridorCore]
      have parts :=
        unitSteps_cons_cons_cons unitSteps
      have centerDifferent : sourceCenter ≠ center := by
        simpa using
          (show sourceCenter ≠ center ∧
              sourceCenter ≠ next from
            (by simpa using sourceCenterFresh)).1
      exact
        ribbonMacrocellRoutes_strictlyAvoidEachOther_of_centers_ne_of_colors_ne
          centerDifferent
          sourceIncomingGenuine sourceOutgoingGenuine sourceNoReverse
          (AxisDirection.between_isGenuine_of_unitAxisStep
            parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep
            parts.2.1)
          noReversal.1 colorsDifferent
  | cons fourth rest tailInduction =>
      rw [ribbonCorridorCore]
      have parts :=
        unitSteps_cons_cons_cons unitSteps
      have freshParts :
          sourceCenter ≠ center ∧
            sourceCenter ∉ next :: fourth :: rest := by
        simpa using sourceCenterFresh
      have firstAvoid :
          RoutesStrictlyAvoidEachOther
            (ribbonMacrocellRoute sourceCenter
              sourceIncoming sourceOutgoing sourceColor)
            (ribbonMacrocellRoute center
              (AxisDirection.between first center)
              (AxisDirection.between center next)
              corridorColor) :=
        ribbonMacrocellRoutes_strictlyAvoidEachOther_of_centers_ne_of_colors_ne
          freshParts.1
          sourceIncomingGenuine sourceOutgoingGenuine sourceNoReverse
          (AxisDirection.between_isGenuine_of_unitAxisStep
            parts.1)
          (AxisDirection.between_isGenuine_of_unitAxisStep
            parts.2.1)
          noReversal.1 colorsDifferent
      have tailAvoid :=
        tailInduction center next fourth
          parts.2.2 noReversal.2 freshParts.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          parts.2.1 corridorColor
      apply firstAvoid.join_right tailAvoid
        (ribbonMacrocellRoute_getLast? center
          (AxisDirection.between first center)
          (AxisDirection.between center next)
          corridorColor)
      rw [shared]
      exact
        ribbonCorridorCore_head? corridorColor
          center next fourth rest

/-- Differently colored corridor cores along one duplicate-free unit-step
source route are separated without any contact. -/
theorem ribbonCorridorCores_strictlyAvoidEachOther
    {firstColor secondColor : WireColor}
    (colorsDifferent : firstColor ≠ secondColor)
    (first second : Cell) (rest : List Cell)
    (unitSteps :
      (first :: second :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (first :: second :: rest))
    (nodup : (first :: second :: rest).Nodup) :
    RoutesStrictlyAvoidEachOther
      (ribbonCorridorCore firstColor
        (first :: second :: rest))
      (ribbonCorridorCore secondColor
        (first :: second :: rest)) := by
  induction rest generalizing first second with
  | nil =>
      have firstStep :=
        (List.isChain_cons_cons.mp unitSteps).1
      have directionGenuine :=
        AxisDirection.between_isGenuine_of_unitAxisStep
          firstStep
      have endpointDifferent :
          ribbonMacrocellExit first
              (AxisDirection.between first second)
              firstColor ≠
            ribbonMacrocellExit first
              (AxisDirection.between first second)
              secondColor := by
        intro equal
        apply colorsDifferent
        exact
          color_eq_of_sameCenterRibbonMacrocellEndpoints_eq
            first directionGenuine directionGenuine
            (AxisDirection.ne_opposite_of_isGenuine
              directionGenuine)
            firstColor secondColor .exit .exit equal
      simp [RoutesStrictlyAvoidEachOther,
        ribbonCorridorCoreStart,
        gridPolylineSegments,
        endpointDifferent]
  | cons next rest tailInduction =>
      cases rest with
      | nil =>
          rw [ribbonCorridorCore, ribbonCorridorCore]
          have parts :=
            unitSteps_cons_cons_cons unitSteps
          exact
            sameRibbonMacrocellRoutes_strictlyAvoidEachOther
              second
              (AxisDirection.between_isGenuine_of_unitAxisStep
                parts.1)
              (AxisDirection.between_isGenuine_of_unitAxisStep
                parts.2.1)
              noReversal.1 colorsDifferent
      | cons fourth rest =>
          rw [ribbonCorridorCore, ribbonCorridorCore]
          have parts :=
            unitSteps_cons_cons_cons unitSteps
          have incomingGenuine :=
            AxisDirection.between_isGenuine_of_unitAxisStep
              parts.1
          have outgoingGenuine :=
            AxisDirection.between_isGenuine_of_unitAxisStep
              parts.2.1
          have headAvoid :=
            sameRibbonMacrocellRoutes_strictlyAvoidEachOther
              second incomingGenuine outgoingGenuine
              noReversal.1 colorsDifferent
          have sourceCenterFresh :
              second ∉ next :: fourth :: rest :=
            (List.nodup_cons.mp nodup.tail).1
          have firstHeadAvoidsSecondTail :=
            ribbonMacrocellRoute_strictlyAvoids_ribbonCorridorCore
              (sourceCenter := second)
              (sourceIncoming :=
                AxisDirection.between first second)
              (sourceOutgoing :=
                AxisDirection.between second next)
              incomingGenuine outgoingGenuine noReversal.1
              colorsDifferent
              second next fourth rest
              parts.2.2 noReversal.2 sourceCenterFresh
          have secondHeadAvoidsFirstTail :=
            ribbonMacrocellRoute_strictlyAvoids_ribbonCorridorCore
              (sourceCenter := second)
              (sourceIncoming :=
                AxisDirection.between first second)
              (sourceOutgoing :=
                AxisDirection.between second next)
              incomingGenuine outgoingGenuine noReversal.1
              colorsDifferent.symm
              second next fourth rest
              parts.2.2 noReversal.2 sourceCenterFresh
          have tailAvoid :=
            tailInduction second next
              parts.2.2 noReversal.2 nodup.tail
          have firstShared :=
            ribbonMacrocellExit_eq_entry_of_unitAxisStep
              parts.2.1 firstColor
          have firstTailHead :
              (ribbonCorridorCore firstColor
                (second :: next :: fourth :: rest)).head? =
                  some (ribbonMacrocellExit second
                    (AxisDirection.between second next)
                    firstColor) := by
            rw [firstShared]
            exact
              ribbonCorridorCore_head? firstColor
                second next fourth rest
          have secondShared :=
            ribbonMacrocellExit_eq_entry_of_unitAxisStep
              parts.2.1 secondColor
          have secondTailHead :
              (ribbonCorridorCore secondColor
                (second :: next :: fourth :: rest)).head? =
                  some (ribbonMacrocellExit second
                    (AxisDirection.between second next)
                    secondColor) := by
            rw [secondShared]
            exact
              ribbonCorridorCore_head? secondColor
                second next fourth rest
          have assembledFirstAvoidsSecondHead :=
            headAvoid.join_left
              secondHeadAvoidsFirstTail.symm
              (ribbonMacrocellRoute_getLast? second
                (AxisDirection.between first second)
                (AxisDirection.between second next)
                firstColor)
              firstTailHead
          have assembledFirstAvoidsSecondTail :=
            firstHeadAvoidsSecondTail.join_left
              tailAvoid
              (ribbonMacrocellRoute_getLast? second
                (AxisDirection.between first second)
                (AxisDirection.between second next)
                firstColor)
              firstTailHead
          exact
            assembledFirstAvoidsSecondHead.join_right
              assembledFirstAvoidsSecondTail
              (ribbonMacrocellRoute_getLast? second
                (AxisDirection.between first second)
                (AxisDirection.between second next)
                secondColor)
              secondTailHead

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
