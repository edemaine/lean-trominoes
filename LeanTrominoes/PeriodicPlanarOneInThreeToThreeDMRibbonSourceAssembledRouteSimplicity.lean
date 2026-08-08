import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceOccurrenceRouteSimplicity
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreClauseStubSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRouteSimplicity

/-!
# Simplicity of assembled routed incidences

This file closes the geometric splice between a finite variable-site route
and its coordinated variable-fan, corridor, and clause-fan suffix.  The
finite prefix is simple, the advertised variable port is the only common
listed point, and therefore the complete assembled routed incidence is
simple whenever its unit source route has length at least three.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A routed variable-site prefix remains simple after translation into its
constructed source coordinates. -/
theorem constructedRoutedVariablePrefix_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (constructedRoutedVariablePrefix placement entry color) := by
  have localSimple :
      LocalIncidenceDrawing.RouteIsSimple
        (typedVariableSiteRoute source.erase entry.1.1 entry.atom_mem
          entry.1.2 entry.slot_mem
          (routedOccurrenceTriple source.erase
            entry.1.1 entry.1.2 color)
          (routedOccurrenceTriple_mem_occurrenceTriples
            source.erase entry.1.1 entry.1.2 color)
          color) := by
    exact
      (sourceVariableSiteDrawing_isValid
        source.erase entry.1.1 entry.atom_mem).2.2.1
          (routedActiveVariableSiteTriple source.erase entry color, color)
  simpa [constructedRoutedVariablePrefix, translatePolyline] using
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      localSimple
      (constructedVariableOrigin placement
        standardThreeStrandLayout entry.1.1)

/-- The constructed routed variable prefix ends at the advertised port of
the source-level coordinated occurrence route. -/
theorem constructedRoutedVariablePrefix_getLast?
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (constructedRoutedVariablePrefix placement entry color).getLast? =
      some
        (Cell.add
          (constructedVariableOrigin placement
            standardThreeStrandLayout entry.1.1)
          (routedVariablePortPosition source.erase entry color)) := by
  have endpoints :=
    typedVariableSiteRoute_endpoints source.erase
      entry.1.1 entry.atom_mem entry.1.2 entry.slot_mem
      (routedOccurrenceTriple source.erase entry.1.1 entry.1.2 color)
      (routedOccurrenceTriple_mem_occurrenceTriples
        source.erase entry.1.1 entry.1.2 color)
      color
  simpa [constructedRoutedVariablePrefix, translatePolyline,
    routedVariablePortPosition, routedActiveVariableSiteTriple] using
      congrArg
        (Option.map
          (Cell.add
            (constructedVariableOrigin placement
              standardThreeStrandLayout entry.1.1)))
        endpoints.2

/-- The variable port is the only listed point shared by the constructed
finite prefix and the complete coordinated variable stub. -/
theorem constructedRoutedVariablePrefix_coordinatedVariableStub_only_common
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (point : Cell)
    (prefixMember :
      point ∈ constructedRoutedVariablePrefix placement entry color)
    (stubMember :
      point ∈ occurrenceCoordinatedRibbonVariableStub
        presentation entry color) :
    point =
      Cell.add
        (constructedVariableOrigin placement
          standardThreeStrandLayout entry.1.1)
        (routedVariablePortPosition source.erase entry color) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  rw [← translatedRoutedVariableSiteRoute_eq_constructedPrefix
    entry color] at prefixMember
  change point ∈
    translatePolyline
      (ribbonMacrocellOrigin (placement.position entry.1.1))
      (data.coordinatedRoute slot color) at stubMember
  unfold translatePolyline at prefixMember stubMember
  rcases List.mem_map.mp prefixMember with
    ⟨corePoint, coreMember, pointEq⟩
  rcases List.mem_map.mp stubMember with
    ⟨fanPoint, fanMember, secondPointEq⟩
  have localPointEq : corePoint = fanPoint := by
    apply
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.cell_add_left_injective
        (ribbonMacrocellOrigin (placement.position entry.1.1))
    exact pointEq.trans secondPointEq.symm
  subst fanPoint
  have coreEq :=
    data.routedVariableSiteRoute_coordinatedRoute_only_common
      (compatible.1 entry) slot active color corePoint
      (by
        rw [sourceVariableRibbonFanData_routedVariableSiteRoute
          presentation entry color]
        exact coreMember)
      fanMember
  have translatedPointEq :
      point = Cell.add
        (ribbonMacrocellOrigin (placement.position entry.1.1))
        (data.port slot active color) := by
    exact pointEq.symm.trans (congrArg _ coreEq)
  have stubHeadFromTable :
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry color).head? =
        some
          (Cell.add
            (ribbonMacrocellOrigin (placement.position entry.1.1))
            (data.port slot active color)) := by
    simp [occurrenceCoordinatedRibbonVariableStub, data, slot,
      VariableRibbonFanData.coordinatedRoute_head?
        data slot active color,
      translatePolyline]
  have portEq := Option.some.inj
    (stubHeadFromTable.symm.trans
      (occurrenceCoordinatedRibbonVariableStub_endpoints
        presentation compatible entry color).1)
  exact translatedPointEq.trans portEq

/-- The variable port is likewise the only listed point shared by the
constructed prefix and the complete variable-fan/corridor/clause-fan route. -/
theorem constructedRoutedVariablePrefix_occurrenceRoute_only_common
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (point : Cell)
    (prefixMember :
      point ∈ constructedRoutedVariablePrefix placement entry color)
    (routeMember :
      point ∈ RibbonEndpointFanSystem.occurrenceThreeStrandRoute
        (coordinatedSourceRibbonEndpointFanSystem
          presentation.toPlanarIncidencePresentation width compatible)
        entry color) :
    point =
      Cell.add
        (constructedVariableOrigin placement
          standardThreeStrandLayout entry.1.1)
        (routedVariablePortPosition source.erase entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  unfold RibbonEndpointFanSystem.occurrenceThreeStrandRoute at routeMember
  rcases mem_joinAtEndpoint routeMember with routePrefixMember | clauseMember
  · rcases mem_joinAtEndpoint routePrefixMember with
      variableMember | corridorMember
    · exact
        constructedRoutedVariablePrefix_coordinatedVariableStub_only_common
          planar compatible entry color point prefixMember variableMember
    · exact False.elim
        ((constructedRoutedVariablePrefix_strictlyAvoids_occurrenceRibbonCorridorCore
          presentation entry color).2.2.2
            point prefixMember point corridorMember rfl)
  · exact False.elim
      ((constructedRoutedVariablePrefix_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
        presentation compatible entry color).2.2.2
          point prefixMember point clauseMember rfl)

/-- The same complete-route contact theorem stated for the prefix and route
fields used by the coordinated global routing. -/
theorem assembledRoutedVariablePrefix_coordinatedSourceRoute_only_common
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (point : Cell)
    (prefixMember :
      point ∈ assembledRoutedVariablePrefix
        (coordinatedSourceRibbonThreeStrandRouting
          presentation width compatible)
        entry color)
    (routeMember :
      point ∈
        (coordinatedSourceRibbonThreeStrandRouting
          presentation width compatible).route entry color) :
    point =
      Cell.add
        (constructedVariableOrigin placement
          standardThreeStrandLayout entry.1.1)
        (routedVariablePortPosition source.erase entry color) := by
  rw [assembledRoutedVariablePrefix_eq_constructed
    (coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible) rfl entry color] at prefixMember
  rw [coordinatedSourceRibbonThreeStrandRouting_route] at routeMember
  exact constructedRoutedVariablePrefix_occurrenceRoute_only_common
    presentation width compatible entry color point
    prefixMember routeMember

/-- A complete routed typed incidence in the coordinated global assembly is
geometrically simple once the underlying unit source route has length at
least three. -/
theorem assembledRoutedTypedIncidenceRoute_simple_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    LocalIncidenceDrawing.RouteIsSimple
      (assembledTypedIncidenceRoute
        (coordinatedSourceRibbonThreeStrandRouting
          presentation width compatible)
        ⟨routedOccurrenceTriple source.erase entry.1.1 entry.1.2 color,
          routedOccurrenceTriple_mem_triples
            source.erase entry.1.1 entry.1.2
            entry.atom_mem entry.slot_mem color⟩
        color) := by
  let routing :=
    coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
  rw [assembledRoutedTypedIncidenceRoute_eq routing entry color]
  apply
    (constructedRoutedVariablePrefix_simple
      (placement := placement) entry color).joinAtEndpoint_of_only_common
  · exact
      coordinatedSourceRibbonThreeStrandRouting_route_simple_of_length_ge_three
        presentation width compatible entry color lengthGeThree
  · exact assembledRoutedVariablePrefix_avoids_coordinatedSourceRoute
      presentation width compatible entry color
  · exact constructedRoutedVariablePrefix_getLast? entry color
  · exact (routing.route_endpoints entry color).1
  · exact assembledRoutedVariablePrefix_coordinatedSourceRoute_only_common
      presentation width compatible entry color

/-- Every typed incidence route in the coordinated source assembly is
simple when all selected occurrence routes have length at least three.
Nonselected variable incidences and clause incidences inherit simplicity
directly from their translated finite drawings. -/
theorem coordinatedSourceAssembledTypedIncidenceRoute_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (lengthGeThree :
      ∀ entry : ActiveOccurrenceEntry source.erase,
        3 ≤ (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry).length)
    (triple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (assembledTypedIncidenceRoute
        (coordinatedSourceRibbonThreeStrandRouting
          presentation width compatible)
        triple color) := by
  let routing :=
    coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
  change LocalIncidenceDrawing.RouteIsSimple
    (assembledTypedIncidenceRoute routing triple color)
  unfold assembledTypedIncidenceRoute
  split
  next atom slot variant localTriple tripleEq =>
    let member :
        Triple.ordinary atom slot variant localTriple ∈
          triples source.erase :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location :=
        ordinaryTriple_location source.erase atom slot variant
          localTriple member
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      dsimp only
      rw [assembledOrdinaryPrefix_eq_assembledRoutedVariablePrefix
        routing entry color variant localTriple routed.symm]
      have selected :=
        assembledRoutedTypedIncidenceRoute_simple_of_length_ge_three
          presentation width compatible entry color
          (lengthGeThree entry)
      rw [assembledRoutedTypedIncidenceRoute_eq routing entry color]
        at selected
      exact selected
    next notRouted =>
      exact assembledOrdinaryPrefix_simple routing atom slot variant
        localTriple member color
  next atom slot localTriple tripleEq =>
    let member :
        Triple.fixedRed atom slot localTriple ∈ triples source.erase :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location :=
        fixedRedTriple_location source.erase atom slot localTriple member
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      dsimp only
      rw [assembledFixedRedPrefix_eq_assembledRoutedVariablePrefix
        routing entry color localTriple routed.symm]
      have selected :=
        assembledRoutedTypedIncidenceRoute_simple_of_length_ge_three
          presentation width compatible entry color
          (lengthGeThree entry)
      rw [assembledRoutedTypedIncidenceRoute_eq routing entry color]
        at selected
      exact selected
    next notRouted =>
      exact assembledFixedRedPrefix_simple routing atom slot
        localTriple member color
  next clauseIndex set tripleEq =>
    exact assembledClauseRoute_simple routing clauseIndex set color

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
