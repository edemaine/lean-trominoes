import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellContacts

/-!
# Contact-free separation of ribbon macrocells

Complete route separation allows advertised endpoint contacts.  This file
strengthens the ribbon-macrocell certificates to contact-free separation in
the two situations used by corridor assembly: different colors in one tile,
and distinct tile centers for which the classified directed-edge contact is
excluded.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

private def strictLegalRibbonTurns :
    List (AxisDirection × AxisDirection) :=
  [(.east, .east), (.east, .north), (.east, .south),
    (.north, .east), (.north, .north), (.north, .west),
    (.west, .north), (.west, .west), (.west, .south),
    (.south, .east), (.south, .west), (.south, .south)]

private theorem mem_strictLegalRibbonTurns_iff
    (incoming outgoing : AxisDirection) :
    (incoming, outgoing) ∈ strictLegalRibbonTurns ↔
      incoming.IsGenuine ∧ outgoing.IsGenuine ∧
        outgoing ≠ incoming.opposite := by
  cases incoming <;> cases outgoing <;>
    decide

private def strictRibbonWireColors : List WireColor :=
  [.red, .green, .blue]

private theorem mem_strictRibbonWireColors
    (color : WireColor) :
    color ∈ strictRibbonWireColors := by
  cases color <;>
    simp [strictRibbonWireColors]

private def strictRibbonRouteEnds :
    List RibbonMacrocellRouteEnd :=
  [.entry, .exit]

private theorem mem_strictRibbonRouteEnds
    (endpoint : RibbonMacrocellRouteEnd) :
    endpoint ∈ strictRibbonRouteEnds := by
  cases endpoint <;>
    simp [strictRibbonRouteEnds]

private def allOriginSameCenterEndpointColorsExact : Bool :=
  strictLegalRibbonTurns.all fun turn =>
    strictRibbonWireColors.all fun firstColor =>
      strictRibbonWireColors.all fun secondColor =>
        strictRibbonRouteEnds.all fun firstEnd =>
          strictRibbonRouteEnds.all fun secondEnd =>
            decide
              (ribbonMacrocellEndpoint (0, 0)
                    turn.1 turn.2 firstColor firstEnd =
                  ribbonMacrocellEndpoint (0, 0)
                    turn.1 turn.2 secondColor secondEnd →
                firstColor = secondColor)

private theorem allOriginSameCenterEndpointColorsExact_eq_true :
    allOriginSameCenterEndpointColorsExact = true := by
  native_decide

/-- At one center and for one legal turn, equality of two selected
macrocell endpoints forces equality of their colors. -/
theorem color_eq_of_sameCenterRibbonMacrocellEndpoints_eq
    (center : Cell)
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (firstColor secondColor : WireColor)
    (firstEnd secondEnd : RibbonMacrocellRouteEnd)
    (equal :
      ribbonMacrocellEndpoint center incoming outgoing
          firstColor firstEnd =
        ribbonMacrocellEndpoint center incoming outgoing
          secondColor secondEnd) :
    firstColor = secondColor := by
  have firstTranslation :=
    ribbonMacrocellEndpoint_add_center
      center (0, 0) incoming outgoing firstColor firstEnd
  have secondTranslation :=
    ribbonMacrocellEndpoint_add_center
      center (0, 0) incoming outgoing secondColor secondEnd
  have firstTranslation' :
      ribbonMacrocellEndpoint center incoming outgoing
          firstColor firstEnd =
        Cell.add (ribbonMacrocellOrigin center)
          (ribbonMacrocellEndpoint (0, 0) incoming outgoing
            firstColor firstEnd) := by
    simpa [Cell.add] using firstTranslation
  have secondTranslation' :
      ribbonMacrocellEndpoint center incoming outgoing
          secondColor secondEnd =
        Cell.add (ribbonMacrocellOrigin center)
          (ribbonMacrocellEndpoint (0, 0) incoming outgoing
            secondColor secondEnd) := by
    simpa [Cell.add] using secondTranslation
  have originEqual :
      ribbonMacrocellEndpoint (0, 0) incoming outgoing
          firstColor firstEnd =
        ribbonMacrocellEndpoint (0, 0) incoming outgoing
          secondColor secondEnd := by
    apply
      (Cell.add_left_injective
        (ribbonMacrocellOrigin center))
    exact
      firstTranslation'.symm.trans
        (equal.trans secondTranslation')
  have checked :=
    allOriginSameCenterEndpointColorsExact_eq_true
  simp only [allOriginSameCenterEndpointColorsExact,
    List.all_eq_true, decide_eq_true_eq] at checked
  exact
    checked (incoming, outgoing)
      ((mem_strictLegalRibbonTurns_iff incoming outgoing).2
        ⟨incomingGenuine, outgoingGenuine, noReverse⟩)
      firstColor (mem_strictRibbonWireColors firstColor)
      secondColor (mem_strictRibbonWireColors secondColor)
      firstEnd (mem_strictRibbonRouteEnds firstEnd)
      secondEnd (mem_strictRibbonRouteEnds secondEnd)
      originEqual

/-- Distinct colors through the same legal macrocell are separated without
even an endpoint contact. -/
theorem sameRibbonMacrocellRoutes_strictlyAvoidEachOther
    (center : Cell)
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    {firstColor secondColor : WireColor}
    (colorsDifferent : firstColor ≠ secondColor) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute center
        incoming outgoing firstColor)
      (ribbonMacrocellRoute center
        incoming outgoing secondColor) := by
  have avoid :=
    ribbonMacrocellRoutes_avoidEachOther center
      incomingGenuine outgoingGenuine noReverse colorsDifferent
  apply routesStrictlyAvoidEachOther_of_avoid_of_noContact avoid
  intro firstPoint firstMember secondPoint secondMember equal
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstPointEqual⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondPointEqual⟩
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex
      (firstPointEqual.trans
        (equal.trans secondPointEqual.symm))
  rw [firstPointEqual, secondPointEqual] at endpoints
  rcases
      (ribbonMacrocellRoutePointIsEndpoint_iff
        center incoming outgoing firstColor firstPoint).mp
        endpoints.1 with
    firstEntry | firstExit
  · rcases
        (ribbonMacrocellRoutePointIsEndpoint_iff
          center incoming outgoing secondColor secondPoint).mp
          endpoints.2 with
      secondEntry | secondExit
    · apply colorsDifferent
      apply color_eq_of_sameCenterRibbonMacrocellEndpoints_eq
        center incomingGenuine outgoingGenuine noReverse
        firstColor secondColor .entry .entry
      exact firstEntry.symm.trans (equal.trans secondEntry)
    · apply colorsDifferent
      apply color_eq_of_sameCenterRibbonMacrocellEndpoints_eq
        center incomingGenuine outgoingGenuine noReverse
        firstColor secondColor .entry .exit
      exact firstEntry.symm.trans (equal.trans secondExit)
  · rcases
        (ribbonMacrocellRoutePointIsEndpoint_iff
          center incoming outgoing secondColor secondPoint).mp
          endpoints.2 with
      secondEntry | secondExit
    · apply colorsDifferent
      apply color_eq_of_sameCenterRibbonMacrocellEndpoints_eq
        center incomingGenuine outgoingGenuine noReverse
        firstColor secondColor .exit .entry
      exact firstExit.symm.trans (equal.trans secondEntry)
    · apply colorsDifferent
      apply color_eq_of_sameCenterRibbonMacrocellEndpoints_eq
        center incomingGenuine outgoingGenuine noReverse
        firstColor secondColor .exit .exit
      exact firstExit.symm.trans (equal.trans secondExit)

/-- At adjacent distinct centers, excluding all classified directed-edge
contacts strengthens complete separation to contact-free separation. -/
theorem adjacentRibbonMacrocellRoutes_strictlyAvoidEachOther
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
    (firstColor secondColor : WireColor)
    (noEndpointContact :
      ∀ firstEnd secondEnd,
        ¬RibbonMacrocellEndpointContact
          (Cell.sub secondCenter firstCenter)
          firstIncoming firstOutgoing firstColor firstEnd
          secondIncoming secondOutgoing secondColor secondEnd) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute secondCenter
        secondIncoming secondOutgoing secondColor) := by
  have avoid :=
    adjacentCentersRibbonMacrocellRoutes_avoidEachOther adjacent
      firstIncomingGenuine firstOutgoingGenuine firstNoReverse
      secondIncomingGenuine secondOutgoingGenuine secondNoReverse
      firstColor secondColor
  apply routesStrictlyAvoidEachOther_of_avoid_of_noContact avoid
  intro firstPoint firstMember secondPoint secondMember equal
  rcases List.mem_iff_get.mp firstMember with
    ⟨firstIndex, firstPointEqual⟩
  rcases List.mem_iff_get.mp secondMember with
    ⟨secondIndex, secondPointEqual⟩
  have endpoints :=
    avoid.2.2.2 firstIndex secondIndex
      (firstPointEqual.trans
        (equal.trans secondPointEqual.symm))
  rw [firstPointEqual, secondPointEqual] at endpoints
  rcases
      (ribbonMacrocellRoutePointIsEndpoint_iff
        firstCenter firstIncoming firstOutgoing
        firstColor firstPoint).mp endpoints.1 with
    firstEntry | firstExit
  · rcases
        (ribbonMacrocellRoutePointIsEndpoint_iff
          secondCenter secondIncoming secondOutgoing
          secondColor secondPoint).mp endpoints.2 with
      secondEntry | secondExit
    · apply noEndpointContact .entry .entry
      apply
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff adjacent
          firstIncomingGenuine firstOutgoingGenuine firstNoReverse
          secondIncomingGenuine secondOutgoingGenuine secondNoReverse
          firstColor secondColor .entry .entry).mp
      exact firstEntry.symm.trans (equal.trans secondEntry)
    · apply noEndpointContact .entry .exit
      apply
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff adjacent
          firstIncomingGenuine firstOutgoingGenuine firstNoReverse
          secondIncomingGenuine secondOutgoingGenuine secondNoReverse
          firstColor secondColor .entry .exit).mp
      exact firstEntry.symm.trans (equal.trans secondExit)
  · rcases
        (ribbonMacrocellRoutePointIsEndpoint_iff
          secondCenter secondIncoming secondOutgoing
          secondColor secondPoint).mp endpoints.2 with
      secondEntry | secondExit
    · apply noEndpointContact .exit .entry
      apply
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff adjacent
          firstIncomingGenuine firstOutgoingGenuine firstNoReverse
          secondIncomingGenuine secondOutgoingGenuine secondNoReverse
          firstColor secondColor .exit .entry).mp
      exact firstExit.symm.trans (equal.trans secondEntry)
    · apply noEndpointContact .exit .exit
      apply
        (adjacentCentersRibbonMacrocellEndpoints_eq_iff adjacent
          firstIncomingGenuine firstOutgoingGenuine firstNoReverse
          secondIncomingGenuine secondOutgoingGenuine secondNoReverse
          firstColor secondColor .exit .exit).mp
      exact firstExit.symm.trans (equal.trans secondExit)

/-- For arbitrary distinct centers, excluding the classified adjacent
endpoint contact gives contact-free continuous separation. -/
theorem ribbonMacrocellRoutes_strictlyAvoidEachOther_of_centers_ne
    {firstCenter secondCenter : Cell}
    (centersDifferent : firstCenter ≠ secondCenter)
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
    (firstColor secondColor : WireColor)
    (noEndpointContact :
      ∀ firstEnd secondEnd,
        ¬RibbonMacrocellEndpointContact
          (Cell.sub secondCenter firstCenter)
          firstIncoming firstOutgoing firstColor firstEnd
          secondIncoming secondOutgoing secondColor secondEnd) :
    RoutesStrictlyAvoidEachOther
      (ribbonMacrocellRoute firstCenter
        firstIncoming firstOutgoing firstColor)
      (ribbonMacrocellRoute secondCenter
        secondIncoming secondOutgoing secondColor) := by
  rcases
      ribbonMacrocellCenters_eq_or_far_or_adjacent
        firstCenter secondCenter with
    equal | far | adjacent
  · exact (centersDifferent equal).elim
  · have avoid :=
      farRibbonMacrocellRoutes_avoidEachOther far
        firstIncoming firstOutgoing
        secondIncoming secondOutgoing
        firstColor secondColor
    apply routesStrictlyAvoidEachOther_of_avoid_of_noContact avoid
    intro firstPoint firstMember secondPoint secondMember
    exact
      ne_of_inRibbonMacrocells_of_centersFar
        (ribbonMacrocellRoute_points_bounded
          firstCenter firstIncoming firstOutgoing firstColor
          firstPoint firstMember)
        (ribbonMacrocellRoute_points_bounded
          secondCenter secondIncoming secondOutgoing secondColor
          secondPoint secondMember)
        far
  · exact
      adjacentRibbonMacrocellRoutes_strictlyAvoidEachOther adjacent
        firstIncomingGenuine firstOutgoingGenuine firstNoReverse
        secondIncomingGenuine secondOutgoingGenuine secondNoReverse
        firstColor secondColor noEndpointContact

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
