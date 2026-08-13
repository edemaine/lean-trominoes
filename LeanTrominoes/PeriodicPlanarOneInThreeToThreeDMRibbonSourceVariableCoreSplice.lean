/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreCoordinatedFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedStubs
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Source variable-core splice

This file transports the finite variable-site core versus coordinated-fan
certificate into the coordinates of an actual ribbon-ready source.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The route data of a variable-site drawing respects equality of its
dependent count, kind, polarity, and active-triple indices. -/
theorem variableSiteDrawing_route_eq_of_indices_eq
    (firstCount secondCount : Nat)
    (firstKind secondKind : VariableSiteSlot → VariableConnectorKind)
    (firstPolarity secondPolarity : VariableSiteSlot → Bool)
    (firstTriple : ActiveVariableSiteTriple firstCount firstKind)
    (secondTriple : ActiveVariableSiteTriple secondCount secondKind)
    (countEq : firstCount = secondCount)
    (kindEq : firstKind = secondKind)
    (polarityEq : firstPolarity = secondPolarity)
    (tripleEq : firstTriple.1 = secondTriple.1)
    (color : WireColor) :
    (variableSiteDrawing firstCount firstKind firstPolarity).route
        firstTriple color =
      (variableSiteDrawing secondCount secondKind secondPolarity).route
        secondTriple color := by
  subst secondCount
  subst secondKind
  subst secondPolarity
  exact congrArg
    (fun triple =>
      (variableSiteDrawing firstCount firstKind firstPolarity).route
        triple color)
    (Subtype.ext tripleEq)

/-- The finite core route selected by source fan data is the routed typed
variable-site route used by the global assembly. -/
theorem sourceVariableRibbonFanData_routedVariableSiteRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    let data := sourceVariableRibbonFanData presentation entry
    let slot := occurrenceVariableSiteSlot entry.1.2
    let active : data.SlotActive slot :=
      VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
        presentation entry
    translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active color) color) =
      translatePolyline standardThreeStrandLayout.variableOffset
        (typedVariableSiteRoute source.erase entry.1.1 entry.atom_mem
          entry.1.2 entry.slot_mem
          (routedOccurrenceTriple source.erase
            entry.1.1 entry.1.2 color)
          (routedOccurrenceTriple_mem_occurrenceTriples
            source.erase entry.1.1 entry.1.2 color)
          color) := by
  dsimp only
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  apply congrArg
    (translatePolyline standardThreeStrandLayout.variableOffset)
  simp only [typedVariableSiteRoute, sourceVariableSiteDrawing]
  apply variableSiteDrawing_route_eq_of_indices_eq
  · exact VariableRibbonFanData.sourceVariableRibbonFanData_count
      presentation entry
  · rfl
  · rfl
  · exact VariableRibbonFanData.sourceVariableRibbonFanData_routedTriple
      presentation entry color

/-- After placement in the actual source-variable macrocell, the routed
finite core avoids the complete coordinated variable stub and meets it only
at their advertised variable port. -/
theorem sourceRoutedVariableSiteRoute_avoids_coordinatedVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline
        (ribbonMacrocellOrigin (placement.position entry.1.1))
        (translatePolyline standardThreeStrandLayout.variableOffset
          (typedVariableSiteRoute source.erase entry.1.1 entry.atom_mem
            entry.1.2 entry.slot_mem
            (routedOccurrenceTriple source.erase
              entry.1.1 entry.1.2 color)
            (routedOccurrenceTriple_mem_occurrenceTriples
              source.erase entry.1.1 entry.1.2 color)
            color)))
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry color) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  let active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  have localAvoid :=
    data.routedVariableSiteRoute_avoids_coordinatedRoute
      (compatible.1 entry) slot active color
  have translatedAvoid :=
    routesAvoidEachOther_translate localAvoid
      (ribbonMacrocellOrigin (placement.position entry.1.1))
  rw [sourceVariableRibbonFanData_routedVariableSiteRoute
    presentation entry color] at translatedAvoid
  simpa [occurrenceCoordinatedRibbonVariableStub,
    PeriodicOrthocrossing.translatePolyline,
    data, slot] using translatedAvoid

/-- The exact routed variable-site prefix in the refined source coordinates
used by a constructed three-strand routing. -/
def constructedRoutedVariablePrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (placement : PeriodicVariablePlacement Variable)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  translatePolyline
    (constructedVariableOrigin placement
      standardThreeStrandLayout entry.1.1)
    (typedVariableSiteRoute source.erase entry.1.1 entry.atom_mem
      entry.1.2 entry.slot_mem
      (routedOccurrenceTriple source.erase
        entry.1.1 entry.1.2 color)
      (routedOccurrenceTriple_mem_occurrenceTriples
        source.erase entry.1.1 entry.1.2 color)
      color)

/-- Translating first within the standard macrocell and then placing that
macrocell is the constructed variable-origin translation used globally. -/
theorem translatedRoutedVariableSiteRoute_eq_constructedPrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    translatePolyline
        (ribbonMacrocellOrigin (placement.position entry.1.1))
        (translatePolyline standardThreeStrandLayout.variableOffset
          (typedVariableSiteRoute source.erase entry.1.1 entry.atom_mem
            entry.1.2 entry.slot_mem
            (routedOccurrenceTriple source.erase
              entry.1.1 entry.1.2 color)
            (routedOccurrenceTriple_mem_occurrenceTriples
              source.erase entry.1.1 entry.1.2 color)
            color)) =
      constructedRoutedVariablePrefix placement entry color := by
  rw [translatePolyline_add]
  congr 1
  simp [constructedVariableOrigin, ribbonMacrocellOrigin,
    Cell.add, add_comm]

/-- In the exact coordinates consumed by the global assembly, the routed
variable-site prefix has only its advertised port contact with the complete
coordinated source-variable stub. -/
theorem constructedRoutedVariablePrefix_avoids_coordinatedVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesAvoidEachOther
      (constructedRoutedVariablePrefix placement entry color)
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry color) := by
  rw [← translatedRoutedVariableSiteRoute_eq_constructedPrefix
    entry color]
  exact sourceRoutedVariableSiteRoute_avoids_coordinatedVariableStub
    presentation compatible entry color

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
