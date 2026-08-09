import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedCoreFanSeparation

/-!
# Separation of complete translated assembled incidence routes

The finite-core/core and occurrence-route/occurrence-route theorems combine
with both finite-core/occurrence-route orientations.  Decomposing each full
assembled incidence at its certified splice endpoint then proves continuous
interior-contact separation from every nonzero relative period translate.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- An occurrence-selected typed triple is housed in its variable
macrocell. -/
private theorem translated_routedOccurrenceTriple_atom_owner
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (color : WireColor) :
    tripleMacrocellOwner
        (routedOccurrenceTriple source atom slot color) =
      .atom atom := by
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    cases color <;>
    simp [routedOccurrenceTriple, tripleMacrocellOwner, kindEq]

/-- A translated complete occurrence route and a finite core are ordinarily
separated, and any listed contact occurs at the occurrence route's outer
clause tail. -/
theorem assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRoute_and_meets_only_at_tail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    let translatedRoute := translatePolyline
      (ribbonMacrocellOrigin (placement.translation translate))
      (routing.route entry routeColor)
    RoutesAvoidEachOther
        (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
        translatedRoute ∧
      RoutesMeetOnlyAtFirstTail translatedRoute
        (assembledTypedIncidenceCoreRoute routing coreTriple coreColor) := by
  dsimp only
  let planar := presentation.toPlanarIncidencePresentation
  let physical := ribbonMacrocellOrigin (placement.translation translate)
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let variableStub :=
    occurrenceCoordinatedRibbonVariableStub planar entry routeColor
  let corridor := occurrenceRibbonCorridorCore planar entry routeColor
  let clauseStub :=
    occurrenceCoordinatedRibbonClauseStub planar entry routeColor
  have variableAvoid : RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical variableStub) := by
    simpa [routing, physical, variableStub, planar] using
      assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub
        presentation anchorsZero width compatible coreTriple coreColor
        entry translate translateNonzero routeColor
  have corridorAvoid : RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical corridor) := by
    simpa [routing, physical, corridor, planar] using
      assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
        presentation anchorsZero occurrences arity width compatible
        coreTriple coreColor entry translate translateNonzero routeColor
  have clauseAvoid : RoutesAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical clauseStub) := by
    simpa [routing, physical, clauseStub, planar] using
      assembledTypedIncidenceCoreRoute_avoids_translatedOccurrenceCoordinatedRibbonClauseStub
        presentation width compatible coreTriple coreColor entry translate
        routeColor
  have clauseContacts : RoutesMeetOnlyAtFirstTail
      (translatePolyline physical clauseStub)
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor) := by
    simpa [routing, physical, clauseStub, planar] using
      translatedOccurrenceCoordinatedRibbonClauseStub_meets_assembledTypedIncidenceCoreRoute_onlyAtFirstTail
        presentation width compatible coreTriple coreColor entry translate
        routeColor
  have variableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry routeColor
  have corridorEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar entry routeColor
  have clauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible entry routeColor
  have translatedVariableLast :
      (translatePolyline physical variableStub).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_getLast?_eq_some physical _ _ variableEndpoints.2
  have translatedCorridorHead :
      (translatePolyline physical corridor).head? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_head?_eq_some physical _ _ corridorEndpoints.1
  have translatedCorridorLast :
      (translatePolyline physical corridor).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_getLast?_eq_some physical _ _ corridorEndpoints.2
  have translatedClauseHead :
      (translatePolyline physical clauseStub).head? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_head?_eq_some physical _ _ clauseEndpoints.1
  have prefixStrict := variableAvoid.join_right corridorAvoid
    translatedVariableLast translatedCorridorHead
  have prefixLast :
      (joinAtEndpoint
        (translatePolyline physical variableStub)
        (translatePolyline physical corridor)).getLast? =
          some (Cell.add physical
            (ribbonCorridorRouteEnd
              (routedRibbonLane source.erase entry routeColor)
              (occurrenceUnitSourceRoute planar entry))) :=
    joinAtEndpoint_getLast? translatedVariableLast translatedCorridorHead
      translatedCorridorLast
  have fullAvoid := prefixStrict.toRoutesAvoidEachOther
    |>.join_right_of_tail_contact clauseAvoid clauseContacts
      prefixLast translatedClauseHead
  have fullContacts := clauseContacts.join_left_of_strict_prefix
    prefixStrict.symm prefixLast translatedClauseHead
  change
    RoutesAvoidEachOther
        (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
        (translatePolyline physical
          (joinAtEndpoint
            (joinAtEndpoint variableStub corridor) clauseStub)) ∧
      RoutesMeetOnlyAtFirstTail
        (translatePolyline physical
          (joinAtEndpoint
            (joinAtEndpoint variableStub corridor) clauseStub))
        (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
  rw [translatePolyline_joinAtEndpoint, translatePolyline_joinAtEndpoint]
  exact ⟨fullAvoid, fullContacts⟩

/-- Endpoint-aware core/translated-occurrence separation. -/
theorem assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (routing.route entry routeColor)) :=
  (assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRoute_and_meets_only_at_tail
    presentation anchorsZero occurrences arity width compatible
    coreTriple coreColor entry translate translateNonzero routeColor).1

/-- A translated occurrence route can meet a finite core only at its outer
tail. -/
theorem translatedCoordinatedSourceRoute_meets_assembledTypedIncidenceCoreRoute_onlyAtFirstTail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesMeetOnlyAtFirstTail
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (routing.route entry routeColor))
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor) :=
  (assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRoute_and_meets_only_at_tail
    presentation anchorsZero occurrences arity width compatible
    coreTriple coreColor entry translate translateNonzero routeColor).2

/-- A variable-owned core is strictly separated from every nonzero-translated
complete occurrence route. -/
theorem assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedCoordinatedSourceRoute_of_atom_owner
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (routeColor : WireColor)
    (atomOwner :
      ∃ atom, tripleMacrocellOwner coreTriple.1 = .atom atom) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (routing.route entry routeColor)) := by
  dsimp only
  let planar := presentation.toPlanarIncidencePresentation
  let physical := ribbonMacrocellOrigin (placement.translation translate)
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let variableStub :=
    occurrenceCoordinatedRibbonVariableStub planar entry routeColor
  let corridor := occurrenceRibbonCorridorCore planar entry routeColor
  let clauseStub :=
    occurrenceCoordinatedRibbonClauseStub planar entry routeColor
  have variableAvoid : RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical variableStub) := by
    simpa [routing, physical, variableStub, planar] using
      assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub
        presentation anchorsZero width compatible coreTriple coreColor
        entry translate translateNonzero routeColor
  have corridorAvoid : RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical corridor) := by
    simpa [routing, physical, corridor, planar] using
      assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
        presentation anchorsZero occurrences arity width compatible
        coreTriple coreColor entry translate translateNonzero routeColor
  have clauseAvoid : RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical clauseStub) := by
    simpa [routing, physical, clauseStub, planar] using
      assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_atom_owner
        presentation width compatible coreTriple coreColor entry translate
        routeColor atomOwner
  have variableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry routeColor
  have corridorEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar entry routeColor
  have clauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible entry routeColor
  have translatedVariableLast :
      (translatePolyline physical variableStub).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_getLast?_eq_some physical _ _ variableEndpoints.2
  have translatedCorridorHead :
      (translatePolyline physical corridor).head? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_head?_eq_some physical _ _ corridorEndpoints.1
  have translatedCorridorLast :
      (translatePolyline physical corridor).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_getLast?_eq_some physical _ _ corridorEndpoints.2
  have translatedClauseHead :
      (translatePolyline physical clauseStub).head? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_head?_eq_some physical _ _ clauseEndpoints.1
  have prefixAvoid := variableAvoid.join_right corridorAvoid
    translatedVariableLast translatedCorridorHead
  have prefixLast :
      (joinAtEndpoint
        (translatePolyline physical variableStub)
        (translatePolyline physical corridor)).getLast? =
          some (Cell.add physical
            (ribbonCorridorRouteEnd
              (routedRibbonLane source.erase entry routeColor)
              (occurrenceUnitSourceRoute planar entry))) :=
    joinAtEndpoint_getLast? translatedVariableLast translatedCorridorHead
      translatedCorridorLast
  have fullAvoid := prefixAvoid.join_right clauseAvoid
    prefixLast translatedClauseHead
  change RoutesStrictlyAvoidEachOther
    (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
    (translatePolyline physical
      (joinAtEndpoint
        (joinAtEndpoint variableStub corridor) clauseStub))
  rw [translatePolyline_joinAtEndpoint, translatePolyline_joinAtEndpoint]
  exact fullAvoid

/-- Reversing the relative frame gives endpoint-aware separation and the
tail-contact classifier for an occurrence route against a translated core. -/
theorem coordinatedSourceRoute_avoids_translatedAssembledTypedIncidenceCoreRoute_and_meets_only_at_tail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    let translatedCore := translatePolyline
      (ribbonMacrocellOrigin (placement.translation translate))
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
    RoutesAvoidEachOther (routing.route entry routeColor) translatedCore ∧
      RoutesMeetOnlyAtFirstTail
        (routing.route entry routeColor) translatedCore := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let reverseTranslate := Cell.sub (0, 0) translate
  let backwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation reverseTranslate)
  let forwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation translate)
  have reverseNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply translateNonzero
    rcases translate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.sub] at reverseZero ⊢
    exact reverseZero
  have backwards :=
    assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRoute_and_meets_only_at_tail
      presentation anchorsZero occurrences arity width compatible
      coreTriple coreColor entry reverseTranslate reverseNonzero routeColor
  rcases backwards with ⟨backwardsAvoid, backwardsContacts⟩
  have shiftedAvoid :=
    routesAvoidEachOther_translate backwardsAvoid forwardsPhysical
  have shiftedContacts := backwardsContacts.translate forwardsPhysical
  have shiftsCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases translate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, reverseTranslate,
      ribbonMacrocellOrigin, PeriodicVariablePlacement.translation,
      standardThreeStrandLayout, Cell.sub, Cell.add, Cell.scale]
  change RoutesAvoidEachOther
      (translatePolyline forwardsPhysical
        (assembledTypedIncidenceCoreRoute routing coreTriple coreColor))
      (translatePolyline forwardsPhysical
        (translatePolyline backwardsPhysical
          (routing.route entry routeColor))) at shiftedAvoid
  change RoutesMeetOnlyAtFirstTail
      (translatePolyline forwardsPhysical
        (translatePolyline backwardsPhysical
          (routing.route entry routeColor)))
      (translatePolyline forwardsPhysical
        (assembledTypedIncidenceCoreRoute routing coreTriple coreColor))
      at shiftedContacts
  rw [translatePolyline_add, shiftsCancel, translatePolyline_zero]
      at shiftedAvoid shiftedContacts
  refine ⟨?_, ?_⟩
  · simpa [routing, backwardsPhysical, forwardsPhysical] using
      routesAvoidEachOther_comm shiftedAvoid
  · simpa [routing, backwardsPhysical, forwardsPhysical] using
      shiftedContacts

/-- A complete occurrence route is strictly separated from a nonzero-
translated variable-owned core. -/
theorem coordinatedSourceRoute_strictlyAvoids_translatedAssembledTypedIncidenceCoreRoute_of_atom_owner
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (atomOwner :
      ∃ atom, tripleMacrocellOwner coreTriple.1 = .atom atom) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (routing.route entry routeColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let reverseTranslate := Cell.sub (0, 0) translate
  let backwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation reverseTranslate)
  let forwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation translate)
  have reverseNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply translateNonzero
    rcases translate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.sub] at reverseZero ⊢
    exact reverseZero
  have backwards :=
    assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedCoordinatedSourceRoute_of_atom_owner
      presentation anchorsZero occurrences arity width compatible
      coreTriple coreColor entry reverseTranslate reverseNonzero routeColor
      atomOwner
  have shifted := backwards.translatePolyline forwardsPhysical
  have shiftsCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases translate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, reverseTranslate,
      ribbonMacrocellOrigin, PeriodicVariablePlacement.translation,
      standardThreeStrandLayout, Cell.sub, Cell.add, Cell.scale]
  rw [translatePolyline_add, shiftsCancel, translatePolyline_zero] at shifted
  simpa [routing, backwardsPhysical, forwardsPhysical] using shifted.symm

/-- Every finite incidence core avoids every nonzero-translated complete
coordinated occurrence route. -/
theorem assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (routeColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidInteriorContacts
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (routing.route entry routeColor)) := by
  dsimp only
  let planar := presentation.toPlanarIncidencePresentation
  let physical := ribbonMacrocellOrigin (placement.translation translate)
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let variableStub :=
    occurrenceCoordinatedRibbonVariableStub planar entry routeColor
  let corridor := occurrenceRibbonCorridorCore planar entry routeColor
  let clauseStub :=
    occurrenceCoordinatedRibbonClauseStub planar entry routeColor
  have variableAvoid : RoutesAvoidInteriorContacts
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical variableStub) :=
    RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts (by
      simpa [routing, physical, variableStub, planar] using
        assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub
          presentation anchorsZero width compatible coreTriple coreColor
          entry translate translateNonzero routeColor)
  have corridorAvoid : RoutesAvoidInteriorContacts
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical corridor) :=
    RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts (by
      simpa [routing, physical, corridor, planar] using
        assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
          presentation anchorsZero occurrences arity width compatible
          coreTriple coreColor entry translate translateNonzero routeColor)
  have clauseAvoid : RoutesAvoidInteriorContacts
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline physical clauseStub) :=
    RoutesAvoidEachOther.toRoutesAvoidInteriorContacts (by
      simpa [routing, physical, clauseStub, planar] using
        assembledTypedIncidenceCoreRoute_avoids_translatedOccurrenceCoordinatedRibbonClauseStub
          presentation width compatible coreTriple coreColor entry translate
          routeColor)
  have variableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry routeColor
  have corridorEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar entry routeColor
  have clauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible entry routeColor
  have translatedVariableLast :
      (translatePolyline physical variableStub).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_getLast?_eq_some physical _ _ variableEndpoints.2
  have translatedCorridorHead :
      (translatePolyline physical corridor).head? =
        some (Cell.add physical
          (ribbonCorridorRouteStart
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_head?_eq_some physical _ _ corridorEndpoints.1
  have translatedCorridorLast :
      (translatePolyline physical corridor).getLast? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_getLast?_eq_some physical _ _ corridorEndpoints.2
  have translatedClauseHead :
      (translatePolyline physical clauseStub).head? =
        some (Cell.add physical
          (ribbonCorridorRouteEnd
            (routedRibbonLane source.erase entry routeColor)
            (occurrenceUnitSourceRoute planar entry))) :=
    translatePolyline_head?_eq_some physical _ _ clauseEndpoints.1
  have prefixAvoid := variableAvoid.join_right corridorAvoid
    translatedVariableLast translatedCorridorHead
  have prefixLast :
      (joinAtEndpoint
        (translatePolyline physical variableStub)
        (translatePolyline physical corridor)).getLast? =
          some (Cell.add physical
            (ribbonCorridorRouteEnd
              (routedRibbonLane source.erase entry routeColor)
              (occurrenceUnitSourceRoute planar entry))) :=
    joinAtEndpoint_getLast? translatedVariableLast translatedCorridorHead
      translatedCorridorLast
  have fullAvoid := prefixAvoid.join_right clauseAvoid
    prefixLast translatedClauseHead
  change RoutesAvoidInteriorContacts
    (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
    (translatePolyline physical
      (joinAtEndpoint
        (joinAtEndpoint variableStub corridor) clauseStub))
  rw [translatePolyline_joinAtEndpoint, translatePolyline_joinAtEndpoint]
  exact fullAvoid

/-- Reversing the relative frame gives the opposite mixed orientation:
every complete occurrence route avoids a forward-translated finite core. -/
theorem coordinatedSourceRoute_avoids_translatedAssembledTypedIncidenceCoreRouteInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (routeColor : WireColor)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidInteriorContacts
      (routing.route entry routeColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (assembledTypedIncidenceCoreRoute
          routing coreTriple coreColor)) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let reverseTranslate := Cell.sub (0, 0) translate
  let backwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation reverseTranslate)
  let forwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation translate)
  have reverseNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply translateNonzero
    rcases translate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.sub] at reverseZero ⊢
    exact reverseZero
  have backwards :=
    assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRouteInteriors
      presentation anchorsZero occurrences arity width compatible
      coreTriple coreColor entry reverseTranslate reverseNonzero routeColor
  have shifted := backwards.translatePolyline forwardsPhysical
  have shiftsCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases translate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, reverseTranslate,
      ribbonMacrocellOrigin, PeriodicVariablePlacement.translation,
      standardThreeStrandLayout, Cell.sub, Cell.add, Cell.scale]
  rw [translatePolyline_add, shiftsCancel, translatePolyline_zero] at shifted
  simpa [routing, backwardsPhysical, forwardsPhysical] using shifted.symm

/-- Complete assembled typed incidence routes have full endpoint-aware
separation from every nonzero relative period translate. -/
theorem coordinatedSourceAssembledTypedIncidenceRoute_avoids_nonzeroTranslate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (routeLength : ∀ entry : ActiveOccurrenceEntry source.erase,
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length)
    (first second :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (firstColor secondColor : WireColor)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidEachOther
      (assembledTypedIncidenceRoute routing first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (assembledTypedIncidenceRoute routing second secondColor)) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let physical := ribbonMacrocellOrigin (placement.translation translate)
  have coreCore : RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing first firstColor)
      (translatePolyline physical
        (assembledTypedIncidenceCoreRoute routing second secondColor)) := by
    simpa [routing, physical] using
      assembledTypedIncidenceCoreRoute_strictlyAvoids_nonzeroTranslate
        presentation anchorsZero width compatible first second translate
        translateNonzero firstColor secondColor
  rcases assembledTypedIncidenceRoute_eq_core_or_join
      routing first firstColor with firstCore | firstJoined
  · rcases translatePolyline_assembledTypedIncidenceRoute_eq_core_or_join
        routing physical second secondColor with secondCore | secondJoined
    · rw [firstCore, secondCore]
      exact coreCore.toRoutesAvoidEachOther
    · rcases secondJoined with
        ⟨secondEntry, secondBoundary, secondTripleEq, secondCoreLast,
          secondRouteHead, secondEq⟩
      have coreRoutePair :=
        assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRoute_and_meets_only_at_tail
          presentation anchorsZero occurrences arity width compatible
          first firstColor secondEntry translate translateNonzero secondColor
      rcases coreRoutePair with ⟨coreRouteAvoid, routeCoreContacts⟩
      rw [firstCore, secondEq]
      exact coreCore.toRoutesAvoidEachOther.join_right_of_tail_contact
        coreRouteAvoid routeCoreContacts secondCoreLast secondRouteHead
  · rcases firstJoined with
      ⟨firstEntry, firstBoundary, firstTripleEq,
        firstCoreLast, firstRouteHead, firstEq⟩
    rcases translatePolyline_assembledTypedIncidenceRoute_eq_core_or_join
        routing physical second secondColor with secondCore | secondJoined
    · have routeCorePair :=
        coordinatedSourceRoute_avoids_translatedAssembledTypedIncidenceCoreRoute_and_meets_only_at_tail
          presentation anchorsZero occurrences arity width compatible
          firstEntry firstColor second secondColor translate translateNonzero
      rcases routeCorePair with ⟨routeCoreAvoid, routeCoreContacts⟩
      rw [firstEq, secondCore]
      exact RoutesAvoidEachOther.join_left_of_tail_contact
        coreCore routeCoreAvoid routeCoreContacts
        firstCoreLast firstRouteHead
    · rcases secondJoined with
        ⟨secondEntry, secondBoundary, secondTripleEq, secondCoreLast,
          secondRouteHead, secondEq⟩
      have firstAtomOwner :
          ∃ atom, tripleMacrocellOwner first.1 = .atom atom := by
        refine ⟨firstEntry.1.1, ?_⟩
        rw [firstTripleEq]
        exact translated_routedOccurrenceTriple_atom_owner source.erase
          firstEntry.1.1 firstEntry.1.2 firstColor
      have secondAtomOwner :
          ∃ atom, tripleMacrocellOwner second.1 = .atom atom := by
        refine ⟨secondEntry.1.1, ?_⟩
        rw [secondTripleEq]
        exact translated_routedOccurrenceTriple_atom_owner source.erase
          secondEntry.1.1 secondEntry.1.2 secondColor
      have firstCoreSecondRoute : RoutesStrictlyAvoidEachOther
          (assembledTypedIncidenceCoreRoute routing first firstColor)
          (translatePolyline physical
            (routing.route secondEntry secondColor)) := by
        simpa [routing, physical] using
          assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedCoordinatedSourceRoute_of_atom_owner
            presentation anchorsZero occurrences arity width compatible
            first firstColor secondEntry translate translateNonzero
            secondColor firstAtomOwner
      have firstRouteSecondCore : RoutesStrictlyAvoidEachOther
          (routing.route firstEntry firstColor)
          (translatePolyline physical
            (assembledTypedIncidenceCoreRoute
              routing second secondColor)) := by
        simpa [routing, physical] using
          coordinatedSourceRoute_strictlyAvoids_translatedAssembledTypedIncidenceCoreRoute_of_atom_owner
            presentation anchorsZero occurrences arity width compatible
            firstEntry firstColor second secondColor translate
            translateNonzero secondAtomOwner
      have routeRoute : RoutesStrictlyAvoidEachOther
          (routing.route firstEntry firstColor)
          (translatePolyline physical
            (routing.route secondEntry secondColor)) := by
        simpa [routing, physical] using
          coordinatedSourceRibbonThreeStrandRoute_strictlyAvoids_nonzeroTranslate_of_length_ge_three
            presentation width compatible firstEntry secondEntry translate
            translateNonzero (routeLength firstEntry)
            (routeLength secondEntry) firstColor secondColor
      have firstFullSecondCore := coreCore.join_left
        firstRouteSecondCore firstCoreLast firstRouteHead
      have firstFullSecondRoute := firstCoreSecondRoute.join_left
        routeRoute firstCoreLast firstRouteHead
      have fullStrict := firstFullSecondCore.join_right
        firstFullSecondRoute secondCoreLast secondRouteHead
      rw [firstEq, secondEq]
      exact fullStrict.toRoutesAvoidEachOther

/-- Complete assembled typed incidence routes avoid every nonzero relative
period translate of one another. -/
theorem coordinatedSourceAssembledTypedIncidenceRoute_avoids_nonzeroTranslateInteriors
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (routeLength : ∀ entry : ActiveOccurrenceEntry source.erase,
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length)
    (first second :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (firstColor secondColor : WireColor)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidInteriorContacts
      (assembledTypedIncidenceRoute routing first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (assembledTypedIncidenceRoute routing second secondColor)) := by
  dsimp only
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  let physical := ribbonMacrocellOrigin (placement.translation translate)
  have coreCore : RoutesAvoidInteriorContacts
      (assembledTypedIncidenceCoreRoute routing first firstColor)
      (translatePolyline physical
        (assembledTypedIncidenceCoreRoute routing second secondColor)) :=
    RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts (by
      simpa [routing, physical] using
        assembledTypedIncidenceCoreRoute_strictlyAvoids_nonzeroTranslate
          presentation anchorsZero width compatible first second translate
          translateNonzero firstColor secondColor)
  rcases assembledTypedIncidenceRoute_eq_core_or_join
      routing first firstColor with firstCore | firstJoined
  · rcases translatePolyline_assembledTypedIncidenceRoute_eq_core_or_join
        routing physical second secondColor with secondCore | secondJoined
    · rw [firstCore, secondCore]
      exact coreCore
    · rcases secondJoined with
        ⟨secondEntry, secondBoundary, _, secondCoreLast,
          secondRouteHead, secondEq⟩
      have coreRoute :=
        assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRouteInteriors
          presentation anchorsZero occurrences arity width compatible
          first firstColor secondEntry translate translateNonzero secondColor
      rw [firstCore, secondEq]
      exact coreCore.join_right (by simpa [routing, physical] using coreRoute)
        secondCoreLast secondRouteHead
  · rcases firstJoined with
      ⟨firstEntry, firstBoundary, _, firstCoreLast, firstRouteHead, firstEq⟩
    have routeCore :=
      coordinatedSourceRoute_avoids_translatedAssembledTypedIncidenceCoreRouteInteriors
        presentation anchorsZero occurrences arity width compatible
        firstEntry firstColor second secondColor translate translateNonzero
    rcases translatePolyline_assembledTypedIncidenceRoute_eq_core_or_join
        routing physical second secondColor with secondCore | secondJoined
    · rw [firstEq, secondCore]
      exact coreCore.join_left (by simpa [routing, physical] using routeCore)
        firstCoreLast firstRouteHead
    · rcases secondJoined with
        ⟨secondEntry, secondBoundary, _, secondCoreLast,
          secondRouteHead, secondEq⟩
      have coreRoute :=
        assembledTypedIncidenceCoreRoute_avoids_translatedCoordinatedSourceRouteInteriors
          presentation anchorsZero occurrences arity width compatible
          first firstColor secondEntry translate translateNonzero secondColor
      have routeRoute :=
        coordinatedSourceRibbonThreeStrandRoute_strictlyAvoids_nonzeroTranslate_of_length_ge_three
          presentation width compatible firstEntry secondEntry translate
          translateNonzero (routeLength firstEntry) (routeLength secondEntry)
          firstColor secondColor
      have firstFullAvoidsSecondCore :=
        coreCore.join_left (by simpa [routing, physical] using routeCore)
          firstCoreLast firstRouteHead
      have firstFullAvoidsSecondRoute :=
        (by
          exact (by simpa [routing, physical] using
            (RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts
              routeRoute)) :
            RoutesAvoidInteriorContacts
              (routing.route firstEntry firstColor)
              (translatePolyline physical
                (routing.route secondEntry secondColor)))
      have firstFullAvoidsSecondRoute' :=
        (by
          have corePart : RoutesAvoidInteriorContacts
              (assembledTypedIncidenceCoreRoute routing first firstColor)
              (translatePolyline physical
                (routing.route secondEntry secondColor)) := by
            simpa [routing, physical] using coreRoute
          exact corePart.join_left firstFullAvoidsSecondRoute
            firstCoreLast firstRouteHead)
      rw [firstEq, secondEq]
      exact firstFullAvoidsSecondCore.join_right firstFullAvoidsSecondRoute'
        secondCoreLast secondRouteHead

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
