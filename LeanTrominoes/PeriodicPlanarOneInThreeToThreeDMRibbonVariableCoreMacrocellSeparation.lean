import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreCoordinatedFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanMacrocellSeparation

/-!
# Variable-site cores versus corridor macrocells

The routed finite variable-site core stays in its owning standard ribbon
macrocell.  Exhaustive finite certificates show that it has no contact with
the outgoing ribbon boundary points or with any legal corridor tile in one
of the eight neighboring macrocells.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

/-- Every routed finite variable-site core remains in the standard ribbon
macrocell after applying the standard variable offset. -/
theorem routedVariableSiteRoute_points_bounded :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot)
      (active : slot.index < countPred + 1)
      (color : WireColor)
      (point : Cell),
      point ∈
          translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing (countPred + 1) kind polarity).route
              ⟨(VariableRibbonFanData.routedTriple
                  ⟨countPred, kind, polarity, fun _ => .invalid⟩
                  slot color),
                VariableRibbonFanData.routedTriple_matches
                  ⟨countPred, kind, polarity, fun _ => .invalid⟩
                  slot active color⟩
              color) →
        InStandardRibbonMacrocell point := by
  native_decide

/-- A routed finite variable-site core has no contact with any standard
ribbon exit point. -/
theorem routedVariableSiteRoute_strictlyAvoids_ribbonMacrocellExit :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot)
      (active : slot.index < countPred + 1)
      (color : WireColor)
      (direction : AxisDirection)
      (lane : WireColor),
      RoutesStrictlyAvoidEachOther
        (translatePolyline standardThreeStrandLayout.variableOffset
          ((variableSiteDrawing (countPred + 1) kind polarity).route
            ⟨(VariableRibbonFanData.routedTriple
                ⟨countPred, kind, polarity, fun _ => .invalid⟩
                slot color),
              VariableRibbonFanData.routedTriple_matches
                ⟨countPred, kind, polarity, fun _ => .invalid⟩
                slot active color⟩
            color))
        [standardRibbonMacrocellExit direction lane] := by
  native_decide

/-- A routed finite variable-site core has no contact with any legal ribbon
tile in a neighboring macrocell. -/
theorem routedVariableSiteRoute_strictlyAvoids_adjacentRibbonMacrocellRoute :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot)
      (active : slot.index < countPred + 1)
      (color : WireColor)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      (incoming outgoing : AxisDirection)
      (tileColor : WireColor),
      incoming.IsGenuine → outgoing.IsGenuine →
      outgoing ≠ incoming.opposite →
      RoutesStrictlyAvoidEachOther
        (translatePolyline standardThreeStrandLayout.variableOffset
          ((variableSiteDrawing (countPred + 1) kind polarity).route
            ⟨(VariableRibbonFanData.routedTriple
                ⟨countPred, kind, polarity, fun _ => .invalid⟩
                slot color),
              VariableRibbonFanData.routedTriple_matches
                ⟨countPred, kind, polarity, fun _ => .invalid⟩
                slot active color⟩
            color))
        (ribbonMacrocellRoute
          (ribbonAdjacentMacrocellOffsets.get offsetIndex)
          incoming outgoing tileColor) := by
  native_decide +revert

namespace VariableRibbonFanData

/-- Data-packaged point bound for a routed finite variable-site core. -/
theorem routedVariableSiteRoute_points_bounded
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    {point : Cell}
    (member :
      point ∈
        translatePolyline standardThreeStrandLayout.variableOffset
          ((variableSiteDrawing data.count data.kind data.polarity).route
            (data.activeRoutedTriple slot active color) color)) :
    InStandardRibbonMacrocell point := by
  exact LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.routedVariableSiteRoute_points_bounded
    data.countPred data.kind data.polarity slot active color point member

/-- Data-packaged separation from a standard ribbon exit point. -/
theorem routedVariableSiteRoute_strictlyAvoids_ribbonMacrocellExit
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (direction : AxisDirection)
    (lane : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active color) color))
      [standardRibbonMacrocellExit direction lane] := by
  exact LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.routedVariableSiteRoute_strictlyAvoids_ribbonMacrocellExit
    data.countPred data.kind data.polarity slot active color direction lane

/-- Data-packaged separation from a legal neighboring ribbon tile. -/
theorem routedVariableSiteRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (offset : Cell)
    (adjacent : RibbonMacrocellOffsetAdjacent offset)
    (incoming outgoing : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (tileColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active color) color))
      (ribbonMacrocellRoute offset incoming outgoing tileColor) := by
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff offset).2 adjacent) with
    ⟨offsetIndex, offsetEq⟩
  rw [← offsetEq]
  exact LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM.routedVariableSiteRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
    data.countPred data.kind data.polarity slot active color
    offsetIndex incoming outgoing tileColor
    incomingGenuine outgoingGenuine noReverse

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
