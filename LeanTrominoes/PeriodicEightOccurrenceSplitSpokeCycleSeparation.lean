import LeanTrominoes.OccurrenceSplitRingSpokeCycleSeparation
import LeanTrominoes.OccurrenceSplitAngularFanSpokeSeparation
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleDrawing
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation

/-!
# Positioned occurrence spokes avoid translated implication cycles

The old-incidence spoke and its Figure 7 implication ring use a common
macrocell origin.  A periodic literal occurrence adds the same placement
translation to both.  This module transports the exact local mixed
certificate through that common positioning, without forbidding the legal
shared ring-vertex endpoint.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- A positioned occurrence spoke continuously avoids any route selected
from the correspondingly translated implication ring. -/
theorem angularFanSpokeRouteAt_avoids_translatedPositionedCycleRoutes
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (logicalOffset : Cell)
    (occurrenceIndex cycleClauseIndex literalIndex : Nat) :
    RoutesAvoidEachOther
      (angularFanSpokeRouteAt sourcePlacement atom
        logicalOffset occurrenceIndex)
      (translatePolyline
        ((placement sourcePlacement).translation logicalOffset)
        (positionedCycleRoutes sourcePlacement atom
          cycleClauseIndex literalIndex)) := by
  have localAvoid :=
    spokeRoute_avoids_cycleRoutes
      (angularPortOfIndex occurrenceIndex)
      cycleClauseIndex literalIndex
  have cycleEq :
      translatePolyline
          ((placement sourcePlacement).translation logicalOffset)
          (positionedCycleRoutes sourcePlacement atom
            cycleClauseIndex literalIndex) =
        (cycleRoutes cycleClauseIndex literalIndex).map
          (Cell.add
            (angularFanOccurrenceOrigin sourcePlacement
              atom logicalOffset)) := by
    unfold translatePolyline positionedCycleRoutes
      translatedCycleDrawing cycleDrawing
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.translate
    simp only [List.map_map]
    apply List.map_congr_left
    intro point _pointMember
    rcases point with ⟨pointX, pointY⟩
    rcases macroEq : macroOrigin sourcePlacement atom with
      ⟨macroX, macroY⟩
    rcases translationEq :
        (placement sourcePlacement).translation logicalOffset with
      ⟨translationX, translationY⟩
    simp [angularFanOccurrenceOrigin, macroEq,
      translationEq, Cell.add]
    constructor <;> ring
  rw [angularFanSpokeRouteAt_eq_map_add, cycleEq]
  exact
    routesAvoidEachOther_translate
      localAvoid
      (angularFanOccurrenceOrigin sourcePlacement
        atom logicalOffset)

/-- Positive uniform refinement preserves the positioned mixed
spoke/cycle certificate. -/
theorem scaledAngularFanSpokeRouteAt_avoids_scaledTranslatedPositionedCycleRoutes
    {Variable : Type*}
    (factor : Int)
    (factorPositive : 0 < factor)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    (logicalOffset : Cell)
    (occurrenceIndex cycleClauseIndex literalIndex : Nat) :
    RoutesAvoidEachOther
      (scalePolyline factor
        (angularFanSpokeRouteAt sourcePlacement atom
          logicalOffset occurrenceIndex))
      (scalePolyline factor
        (translatePolyline
          ((placement sourcePlacement).translation logicalOffset)
          (positionedCycleRoutes sourcePlacement atom
            cycleClauseIndex literalIndex))) :=
  (angularFanSpokeRouteAt_avoids_translatedPositionedCycleRoutes
    sourcePlacement atom logicalOffset occurrenceIndex
    cycleClauseIndex literalIndex).scalePolyline factorPositive

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
