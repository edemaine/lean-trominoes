/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCoreStubSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSplice
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMPolarityNormalization

/-!
# Source variable cores versus coordinated variable fans

The finite variable-site theorem applies to every core route, not just the
route selected by the occurrence being fanned out.  This file transports that
stronger endpoint-aware statement into source coordinates.  At one source
variable all listed contacts remain advertised endpoints; distinct variable
macrocells are separated strictly by their inset bounds.  Interior-only
projections are retained for the continuous-planarity assembly API.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing
open PeriodicOneInThreePolarityNormalization

/-- Every route in one source variable site avoids the segment interiors of
every coordinated fan belonging to that same variable. -/
theorem sourceVariableSiteRoute_avoids_coordinatedVariableStubInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1))
    (coreColor routeColor : WireColor) :
    RoutesAvoidInteriorContacts
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          entry.1.1)
        ((sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry routeColor) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  rcases exists_occurrenceAt_of_mem_usedSlots source.erase
      entry.1.1 entry.1.2 entry.slot_mem with ⟨tagged, lookup⟩
  have clear : VariableLocalGateTableEndpointClear
      (data.kind slot) (data.polarity slot) := by
    simpa [data, slot] using
      occurrenceConnectorPolarity_pattern source.erase width normalized
        entry.1.1 entry.1.2 tagged lookup
  let dataTriple : ActiveVariableSiteTriple data.count data.kind :=
    ⟨triple.1, by
      rw [VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry]
      change VariableSiteTriple.MatchesKind
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1) triple.1
      exact triple.2⟩
  have localAvoid :=
    data.variableSiteRoute_avoids_coordinatedRouteInteriors
      (compatible.1 entry) slot active dataTriple coreColor routeColor clear
  have coreEq :
      (variableSiteDrawing data.count data.kind data.polarity).route
          dataTriple coreColor =
        (sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor := by
    unfold sourceVariableSiteDrawing
    apply variableSiteDrawing_route_eq_of_indices_eq
    · exact VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry
    · rfl
    · rfl
    · rfl
  have translatedAvoid :=
    localAvoid.translatePolyline
      (ribbonMacrocellOrigin (placement.position entry.1.1))
  simpa [data, slot, occurrenceCoordinatedRibbonVariableStub,
    constructedVariableOrigin, ribbonMacrocellOrigin,
    translatePolyline_add, coreEq, Cell.add, add_comm] using
      translatedAvoid

/-- Every route in one source variable site has complete endpoint-aware
separation from every coordinated fan belonging to that same variable. -/
theorem sourceVariableSiteRoute_avoids_coordinatedVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1))
    (coreColor routeColor : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          entry.1.1)
        ((sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry routeColor) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  rcases exists_occurrenceAt_of_mem_usedSlots source.erase
      entry.1.1 entry.1.2 entry.slot_mem with ⟨tagged, lookup⟩
  have clear : VariableLocalGateTableEndpointClear
      (data.kind slot) (data.polarity slot) := by
    simpa [data, slot] using
      occurrenceConnectorPolarity_pattern source.erase width normalized
        entry.1.1 entry.1.2 tagged lookup
  let dataTriple : ActiveVariableSiteTriple data.count data.kind :=
    ⟨triple.1, by
      rw [VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry]
      change VariableSiteTriple.MatchesKind
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1) triple.1
      exact triple.2⟩
  have localAvoid :=
    data.variableSiteRoute_avoids_coordinatedRoute_of_endpointClear
      (compatible.1 entry) slot active dataTriple coreColor routeColor clear
  have coreEq :
      (variableSiteDrawing data.count data.kind data.polarity).route
          dataTriple coreColor =
        (sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor := by
    unfold sourceVariableSiteDrawing
    apply variableSiteDrawing_route_eq_of_indices_eq
    · exact VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry
    · rfl
    · rfl
    · rfl
  have translatedAvoid :
      RoutesAvoidEachOther
        (translatePolyline
          (ribbonMacrocellOrigin (placement.position entry.1.1))
          (translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing data.count data.kind data.polarity).route
              dataTriple coreColor)))
        (translatePolyline
          (ribbonMacrocellOrigin (placement.position entry.1.1))
          (data.coordinatedRoute slot routeColor)) := by
    simpa [PeriodicOrthocrossing.translatePolyline] using
      routesAvoidEachOther_translate localAvoid
        (ribbonMacrocellOrigin (placement.position entry.1.1))
  simpa [data, slot, occurrenceCoordinatedRibbonVariableStub,
    constructedVariableOrigin, ribbonMacrocellOrigin,
    translatePolyline_add, coreEq, Cell.add, add_comm] using
      translatedAvoid

/-- Within one source variable, a core route is contact-free from a
coordinated fan unless it is that fan's selected colored route. -/
theorem sourceVariableSiteRoute_strictlyAvoids_coordinatedVariableStub_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1))
    (coreColor routeColor : WireColor)
    (different :
      (triple.1, coreColor) ≠
        (variableSiteTripleOfTyped
          (routedOccurrenceTriple source.erase
            entry.1.1 entry.1.2 routeColor),
          routeColor)) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          entry.1.1)
        ((sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry routeColor) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  rcases exists_occurrenceAt_of_mem_usedSlots source.erase
      entry.1.1 entry.1.2 entry.slot_mem with ⟨tagged, lookup⟩
  have clear : VariableLocalGateTableEndpointClear
      (data.kind slot) (data.polarity slot) := by
    simpa [data, slot] using
      occurrenceConnectorPolarity_pattern source.erase width normalized
        entry.1.1 entry.1.2 tagged lookup
  let dataTriple : ActiveVariableSiteTriple data.count data.kind :=
    ⟨triple.1, by
      rw [VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry]
      change VariableSiteTriple.MatchesKind
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1) triple.1
      exact triple.2⟩
  have localDifferent :
      (dataTriple.1, coreColor) ≠
        (data.routedTriple slot routeColor, routeColor) := by
    simpa [dataTriple, data, slot] using different
  have localAvoid :=
    data.variableSiteRoute_strictlyAvoids_coordinatedRoute_of_ne
      (compatible.1 entry) slot active dataTriple coreColor routeColor clear
      localDifferent
  have coreEq :
      (variableSiteDrawing data.count data.kind data.polarity).route
          dataTriple coreColor =
        (sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor := by
    unfold sourceVariableSiteDrawing
    apply variableSiteDrawing_route_eq_of_indices_eq
    · exact VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry
    · rfl
    · rfl
    · rfl
  have translatedAvoid :=
    localAvoid.translatePolyline
      (ribbonMacrocellOrigin (placement.position entry.1.1))
  simpa [data, slot, occurrenceCoordinatedRibbonVariableStub,
    constructedVariableOrigin, ribbonMacrocellOrigin,
    translatePolyline_add, coreEq, Cell.add, add_comm] using
      translatedAvoid

/-- Within one source variable, a core route and a coordinated fan from a
different occurrence module have complete endpoint-aware separation. -/
theorem sourceVariableSiteRoute_avoids_coordinatedVariableStub_of_slot_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1))
    (coreColor routeColor : WireColor)
    (differentSlot :
      triple.1.slot ≠ occurrenceVariableSiteSlot entry.1.2) :
    RoutesAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout
          entry.1.1)
        ((sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry routeColor) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  rcases exists_occurrenceAt_of_mem_usedSlots source.erase
      entry.1.1 entry.1.2 entry.slot_mem with ⟨tagged, lookup⟩
  have clear : VariableLocalGateTableEndpointClear
      (data.kind slot) (data.polarity slot) := by
    simpa [data, slot] using
      occurrenceConnectorPolarity_pattern source.erase width normalized
        entry.1.1 entry.1.2 tagged lookup
  let dataTriple : ActiveVariableSiteTriple data.count data.kind :=
    ⟨triple.1, by
      rw [VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry]
      change VariableSiteTriple.MatchesKind
        (sourceVariableSiteCount source.erase entry.1.1)
        (sourceVariableSiteKind source.erase entry.1.1) triple.1
      exact triple.2⟩
  have localAvoid :=
    data.variableSiteRoute_avoids_coordinatedRoute_of_slot_ne
      (compatible.1 entry) slot active dataTriple coreColor routeColor clear
      (by simpa [dataTriple, slot] using differentSlot)
  have coreEq :
      (variableSiteDrawing data.count data.kind data.polarity).route
          dataTriple coreColor =
        (sourceVariableSiteDrawing source.erase entry.1.1).route
          triple coreColor := by
    unfold sourceVariableSiteDrawing
    apply variableSiteDrawing_route_eq_of_indices_eq
    · exact VariableRibbonFanData.sourceVariableRibbonFanData_count
        presentation entry
    · rfl
    · rfl
    · rfl
  have translatedAvoid :
      RoutesAvoidEachOther
        (translatePolyline
          (ribbonMacrocellOrigin (placement.position entry.1.1))
          (translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing data.count data.kind data.polarity).route
              dataTriple coreColor)))
        (translatePolyline
          (ribbonMacrocellOrigin (placement.position entry.1.1))
          (data.coordinatedRoute slot routeColor)) := by
    simpa [PeriodicOrthocrossing.translatePolyline] using
      routesAvoidEachOther_translate localAvoid
        (ribbonMacrocellOrigin (placement.position entry.1.1))
  simpa [data, slot, occurrenceCoordinatedRibbonVariableStub,
    constructedVariableOrigin, ribbonMacrocellOrigin,
    translatePolyline_add, coreEq, Cell.add, add_comm] using
      translatedAvoid

/-- A route in any source variable core avoids the segment interiors of any
coordinated source-variable fan.  Equal owners use the finite all-pairs
certificate; distinct owners are strictly separated macrocells. -/
theorem constructedVariableSiteRoute_avoids_occurrenceCoordinatedRibbonVariableStubInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase atom)
        (sourceVariableSiteKind source.erase atom))
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor) :
    RoutesAvoidInteriorContacts
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout atom)
        ((sourceVariableSiteDrawing source.erase atom).route
          triple coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry routeColor) := by
  by_cases sameAtom : atom = entry.1.1
  · subst atom
    exact
      sourceVariableSiteRoute_avoids_coordinatedVariableStubInteriors
        presentation.toPlanarIncidencePresentation width normalized
        compatible entry
        triple coreColor routeColor
  · have centersNe :
        placement.position atom ≠ placement.position entry.1.1 := by
      exact assemblyMacrocellOwnerPosition_ne_of_ne
        presentation.toPlanarIncidencePresentation anchorsZero
        (.atom atom) (.atom entry.1.1) atomMember entry.atom_mem
        (fun equal => sameAtom (AssemblyMacrocellOwner.atom.inj equal))
    have strict :=
      insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
        (sourceVariableSiteRoute_points_in_inset_rectangle
          source.erase atom atomMember triple coreColor)
        (fun point member =>
          occurrenceCoordinatedRibbonVariableStub_points_bounded
            presentation.toPlanarIncidencePresentation compatible
            entry routeColor member)
        centersNe
    exact RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts (by
      simpa [constructedVariableOrigin, translatePolyline_add,
        ribbonMacrocellOrigin, Cell.add, add_comm] using strict)

/-- A route in any source variable core has complete endpoint-aware
separation from any coordinated source-variable fan.  Equal owners use the
normalized finite all-pairs certificate; distinct owners lie in strictly
separated macrocells. -/
theorem constructedVariableSiteRoute_avoids_occurrenceCoordinatedRibbonVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase atom)
        (sourceVariableSiteKind source.erase atom))
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout atom)
        ((sourceVariableSiteDrawing source.erase atom).route
          triple coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry routeColor) := by
  by_cases sameAtom : atom = entry.1.1
  · subst atom
    exact
      sourceVariableSiteRoute_avoids_coordinatedVariableStub
        presentation.toPlanarIncidencePresentation width normalized
        compatible entry triple coreColor routeColor
  · have centersNe :
        placement.position atom ≠ placement.position entry.1.1 := by
      exact assemblyMacrocellOwnerPosition_ne_of_ne
        presentation.toPlanarIncidencePresentation anchorsZero
        (.atom atom) (.atom entry.1.1) atomMember entry.atom_mem
        (fun equal => sameAtom (AssemblyMacrocellOwner.atom.inj equal))
    have strict :=
      insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
        (sourceVariableSiteRoute_points_in_inset_rectangle
          source.erase atom atomMember triple coreColor)
        (fun point member =>
          occurrenceCoordinatedRibbonVariableStub_points_bounded
            presentation.toPlanarIncidencePresentation compatible
            entry routeColor member)
        centersNe
    exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
      simpa [constructedVariableOrigin, translatePolyline_add,
        ribbonMacrocellOrigin, Cell.add, add_comm] using strict)

/-- A source variable-core route is contact-free from a coordinated fan
whenever, for a common variable owner, it is not that fan's selected
colored route.  Distinct owners remain strictly separated unconditionally. -/
theorem
    constructedVariableSiteRoute_strictlyAvoids_occurrenceCoordinatedRibbonVariableStub_of_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (normalized : FormulaPolarityNormalized source.erase)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (atom : Variable)
    (atomMember : atom ∈ occurringVariables source.erase)
    (triple :
      ActiveVariableSiteTriple
        (sourceVariableSiteCount source.erase atom)
        (sourceVariableSiteKind source.erase atom))
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor)
    (different : atom = entry.1.1 →
      (triple.1, coreColor) ≠
        (variableSiteTripleOfTyped
          (routedOccurrenceTriple source.erase
            entry.1.1 entry.1.2 routeColor),
          routeColor)) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedVariableOrigin placement standardThreeStrandLayout atom)
        ((sourceVariableSiteDrawing source.erase atom).route
          triple coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry routeColor) := by
  by_cases sameAtom : atom = entry.1.1
  · subst atom
    exact
      sourceVariableSiteRoute_strictlyAvoids_coordinatedVariableStub_of_ne
        presentation.toPlanarIncidencePresentation width normalized
        compatible entry triple coreColor routeColor
        (different rfl)
  · have centersNe :
        placement.position atom ≠ placement.position entry.1.1 := by
      exact assemblyMacrocellOwnerPosition_ne_of_ne
        presentation.toPlanarIncidencePresentation anchorsZero
        (.atom atom) (.atom entry.1.1) atomMember entry.atom_mem
        (fun equal => sameAtom (AssemblyMacrocellOwner.atom.inj equal))
    have strict :=
      insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
        (sourceVariableSiteRoute_points_in_inset_rectangle
          source.erase atom atomMember triple coreColor)
        (fun point member =>
          occurrenceCoordinatedRibbonVariableStub_points_bounded
            presentation.toPlanarIncidencePresentation compatible
            entry routeColor member)
        centersNe
    simpa [constructedVariableOrigin, translatePolyline_add,
      ribbonMacrocellOrigin, Cell.add, add_comm] using strict

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
