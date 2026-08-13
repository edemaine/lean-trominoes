/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellBounds

/-!
# Exact contacts between ribbon macrocells

Distinct ribbon tiles already satisfy complete continuous separation.  For
joining many tiles into one corridor, we additionally need to know exactly
when their advertised endpoints can coincide.  This file proves that two
legal tiles at adjacent source centers share an endpoint precisely when both
traverse their common source edge in the same direction and color.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Which advertised endpoint of a ribbon macrocell route is selected. -/
inductive RibbonMacrocellRouteEnd
  | entry
  | exit
  deriving DecidableEq, Fintype, Repr

/-- Select the entry or exit point of one ribbon macrocell route. -/
def ribbonMacrocellEndpoint
    (center : Cell) (incoming outgoing : AxisDirection)
    (color : Gadget.WireColor) :
    RibbonMacrocellRouteEnd → Cell
  | .entry => ribbonMacrocellEntry center incoming color
  | .exit => ribbonMacrocellExit center outgoing color

/-- The two intended endpoint contacts between tiles whose second center is
obtained by adding `offset` to the first. -/
def RibbonMacrocellEndpointContact
    (offset : Cell)
    (firstIncoming firstOutgoing : AxisDirection)
    (firstColor : Gadget.WireColor)
    (firstEnd : RibbonMacrocellRouteEnd)
    (secondIncoming secondOutgoing : AxisDirection)
    (secondColor : Gadget.WireColor)
    (secondEnd : RibbonMacrocellRouteEnd) : Prop :=
  match firstEnd, secondEnd with
  | .exit, .entry =>
      offset = firstOutgoing.step ∧
        secondIncoming = firstOutgoing ∧
        secondColor = firstColor
  | .entry, .exit =>
      offset = firstIncoming.opposite.step ∧
        secondOutgoing = firstIncoming ∧
        secondColor = firstColor
  | _, _ => False

instance
    (offset : Cell)
    (firstIncoming firstOutgoing : AxisDirection)
    (firstColor : Gadget.WireColor)
    (firstEnd : RibbonMacrocellRouteEnd)
    (secondIncoming secondOutgoing : AxisDirection)
    (secondColor : Gadget.WireColor)
    (secondEnd : RibbonMacrocellRouteEnd) :
    Decidable
      (RibbonMacrocellEndpointContact offset
        firstIncoming firstOutgoing firstColor firstEnd
        secondIncoming secondOutgoing secondColor secondEnd) := by
  unfold RibbonMacrocellEndpointContact
  split <;> infer_instance

private def adjacentOffsets : List Cell :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1),
    (0, 1), (1, -1), (1, 0), (1, 1)]

private theorem mem_adjacentOffsets_iff
    (offset : Cell) :
    offset ∈ adjacentOffsets ↔
      RibbonMacrocellOffsetAdjacent offset := by
  rcases offset with ⟨offsetX, offsetY⟩
  simp [adjacentOffsets, RibbonMacrocellOffsetAdjacent]
  omega

private def legalTurns :
    List (AxisDirection × AxisDirection) :=
  [(.east, .east), (.east, .north), (.east, .south),
    (.north, .east), (.north, .north), (.north, .west),
    (.west, .north), (.west, .west), (.west, .south),
    (.south, .east), (.south, .west), (.south, .south)]

private theorem mem_legalTurns_iff
    (incoming outgoing : AxisDirection) :
    (incoming, outgoing) ∈ legalTurns ↔
      incoming.IsGenuine ∧ outgoing.IsGenuine ∧
        outgoing ≠ incoming.opposite := by
  cases incoming <;> cases outgoing <;>
    decide

private def wireColors : List Gadget.WireColor :=
  [.red, .green, .blue]

private theorem mem_wireColors
    (color : Gadget.WireColor) :
    color ∈ wireColors := by
  cases color <;>
    simp [wireColors]

private def routeEnds : List RibbonMacrocellRouteEnd :=
  [.entry, .exit]

private theorem mem_routeEnds
    (endpoint : RibbonMacrocellRouteEnd) :
    endpoint ∈ routeEnds := by
  cases endpoint <;>
    simp [routeEnds]

/-- One executable check of every legal adjacent-center endpoint pair. -/
private def allOriginAdjacentEndpointContactsExact : Bool :=
  adjacentOffsets.all fun offset =>
    legalTurns.all fun firstTurn =>
      legalTurns.all fun secondTurn =>
        wireColors.all fun firstColor =>
          wireColors.all fun secondColor =>
            routeEnds.all fun firstEnd =>
              routeEnds.all fun secondEnd =>
                decide
                  (ribbonMacrocellEndpoint (0, 0)
                        firstTurn.1 firstTurn.2 firstColor firstEnd =
                      ribbonMacrocellEndpoint offset
                        secondTurn.1 secondTurn.2 secondColor secondEnd ↔
                    RibbonMacrocellEndpointContact offset
                      firstTurn.1 firstTurn.2 firstColor firstEnd
                      secondTurn.1 secondTurn.2 secondColor secondEnd)

private theorem allOriginAdjacentEndpointContactsExact_eq_true :
    allOriginAdjacentEndpointContactsExact = true := by
  native_decide

/-- The endpoint-contact classification at the origin. -/
theorem originAdjacentRibbonMacrocellEndpoints_eq_iff
    {offset : Cell}
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    {firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor)
    (firstEnd secondEnd : RibbonMacrocellRouteEnd) :
    ribbonMacrocellEndpoint (0, 0)
          firstIncoming firstOutgoing firstColor firstEnd =
        ribbonMacrocellEndpoint offset
          secondIncoming secondOutgoing secondColor secondEnd ↔
      RibbonMacrocellEndpointContact offset
        firstIncoming firstOutgoing firstColor firstEnd
        secondIncoming secondOutgoing secondColor secondEnd := by
  have checked :=
    allOriginAdjacentEndpointContactsExact_eq_true
  simp only [allOriginAdjacentEndpointContactsExact,
    List.all_eq_true, decide_eq_true_eq] at checked
  exact checked offset
    ((mem_adjacentOffsets_iff offset).2 offsetAdjacent)
    (firstIncoming, firstOutgoing)
    ((mem_legalTurns_iff firstIncoming firstOutgoing).2
      ⟨firstIncomingGenuine, firstOutgoingGenuine,
        firstNoReverse⟩)
    (secondIncoming, secondOutgoing)
    ((mem_legalTurns_iff secondIncoming secondOutgoing).2
      ⟨secondIncomingGenuine, secondOutgoingGenuine,
        secondNoReverse⟩)
    firstColor (mem_wireColors firstColor)
    secondColor (mem_wireColors secondColor)
    firstEnd (mem_routeEnds firstEnd)
    secondEnd (mem_routeEnds secondEnd)

/-- Adding a source center translates either selected macrocell endpoint by
the refined origin of that center. -/
theorem ribbonMacrocellEndpoint_add_center
    (center relative : Cell)
    (incoming outgoing : AxisDirection)
    (color : Gadget.WireColor)
    (endpoint : RibbonMacrocellRouteEnd) :
    ribbonMacrocellEndpoint (Cell.add center relative)
        incoming outgoing color endpoint =
      Cell.add (ribbonMacrocellOrigin center)
        (ribbonMacrocellEndpoint relative
          incoming outgoing color endpoint) := by
  cases endpoint <;>
    unfold ribbonMacrocellEndpoint
      ribbonMacrocellEntry ribbonMacrocellExit
  all_goals
    rcases center with ⟨centerX, centerY⟩
    rcases relative with ⟨relativeX, relativeY⟩
    simp only [ribbonMacrocellOrigin,
      standardThreeStrandLayout, Cell.add, Cell.scale]
    apply Prod.ext <;> dsimp <;> ring

/-- Exact endpoint contacts for arbitrary adjacent source centers. -/
theorem adjacentCentersRibbonMacrocellEndpoints_eq_iff
    {firstCenter secondCenter : Cell}
    (adjacent :
      RibbonMacrocellCentersAdjacent firstCenter secondCenter)
    {firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor)
    (firstEnd secondEnd : RibbonMacrocellRouteEnd) :
    ribbonMacrocellEndpoint firstCenter
          firstIncoming firstOutgoing firstColor firstEnd =
        ribbonMacrocellEndpoint secondCenter
          secondIncoming secondOutgoing secondColor secondEnd ↔
      RibbonMacrocellEndpointContact
        (Cell.sub secondCenter firstCenter)
        firstIncoming firstOutgoing firstColor firstEnd
        secondIncoming secondOutgoing secondColor secondEnd := by
  let offset := Cell.sub secondCenter firstCenter
  have offsetAdjacent :
      RibbonMacrocellOffsetAdjacent offset := by
    exact adjacent
  have secondEquation :
      secondCenter = Cell.add firstCenter offset := by
    rcases firstCenter with ⟨firstX, firstY⟩
    rcases secondCenter with ⟨secondX, secondY⟩
    simp [offset, Cell.sub, Cell.add]
  have recoverOffset :
      Cell.sub (Cell.add firstCenter offset) firstCenter =
        offset := by
    rcases firstCenter with ⟨firstX, firstY⟩
    rcases offset with ⟨offsetX, offsetY⟩
    simp [Cell.sub, Cell.add]
  have firstTranslation :
      ribbonMacrocellEndpoint firstCenter
          firstIncoming firstOutgoing firstColor firstEnd =
        Cell.add (ribbonMacrocellOrigin firstCenter)
          (ribbonMacrocellEndpoint (0, 0)
            firstIncoming firstOutgoing firstColor firstEnd) := by
    simpa [Cell.add] using
      ribbonMacrocellEndpoint_add_center
        firstCenter (0, 0)
        firstIncoming firstOutgoing firstColor firstEnd
  rw [secondEquation, firstTranslation,
    ribbonMacrocellEndpoint_add_center]
  rw [(Cell.add_left_injective
    (ribbonMacrocellOrigin firstCenter)).eq_iff]
  rw [recoverOffset]
  exact
    originAdjacentRibbonMacrocellEndpoints_eq_iff
      offsetAdjacent
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor firstEnd secondEnd

/-- Any endpoint contact between legal tiles at adjacent centers preserves
the ribbon color. -/
theorem color_eq_of_adjacentCentersRibbonMacrocellEndpoints_eq
    {firstCenter secondCenter : Cell}
    (adjacent :
      RibbonMacrocellCentersAdjacent firstCenter secondCenter)
    {firstIncoming firstOutgoing
      secondIncoming secondOutgoing : AxisDirection}
    (firstIncomingGenuine : firstIncoming.IsGenuine)
    (firstOutgoingGenuine : firstOutgoing.IsGenuine)
    (firstNoReverse :
      firstOutgoing ≠ firstIncoming.opposite)
    (secondIncomingGenuine : secondIncoming.IsGenuine)
    (secondOutgoingGenuine : secondOutgoing.IsGenuine)
    (secondNoReverse :
      secondOutgoing ≠ secondIncoming.opposite)
    (firstColor secondColor : Gadget.WireColor)
    (firstEnd secondEnd : RibbonMacrocellRouteEnd)
    (equal :
      ribbonMacrocellEndpoint firstCenter
          firstIncoming firstOutgoing firstColor firstEnd =
        ribbonMacrocellEndpoint secondCenter
          secondIncoming secondOutgoing secondColor secondEnd) :
    firstColor = secondColor := by
  have contact :=
    (adjacentCentersRibbonMacrocellEndpoints_eq_iff adjacent
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor firstEnd secondEnd).mp equal
  cases firstEnd <;> cases secondEnd <;>
    simp_all [RibbonMacrocellEndpointContact]

/-- The generic endpoint predicate on a macrocell route is exactly selection
of its declared entry or exit. -/
theorem ribbonMacrocellRoutePointIsEndpoint_iff
    (center : Cell) (incoming outgoing : AxisDirection)
    (color : Gadget.WireColor) (point : Cell) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
        (ribbonMacrocellRoute center incoming outgoing color) point ↔
      point =
          ribbonMacrocellEndpoint center incoming outgoing color .entry ∨
        point =
          ribbonMacrocellEndpoint center incoming outgoing color .exit := by
  simp [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint,
    ribbonMacrocellEndpoint, eq_comm]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
