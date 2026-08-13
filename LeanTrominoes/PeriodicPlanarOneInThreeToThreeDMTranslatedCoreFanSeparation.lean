/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedCoreCorridorSeparation

/-!
# Separation of finite incidence cores from translated endpoint fans

Strict inset bounds separate a finite incidence core from every translated
variable fan and from every translated clause fan with a distinct center.
If a clause core and translated clause fan have the same lifted center, the
checked finite clause fan/core table supplies the remaining endpoint-only
contact certificate.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Ribbon refinement is additive on macrocell centers. -/
theorem ribbonMacrocellOrigin_add (first second : Cell) :
    ribbonMacrocellOrigin (Cell.add first second) =
      Cell.add (ribbonMacrocellOrigin first)
        (ribbonMacrocellOrigin second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [ribbonMacrocellOrigin, standardThreeStrandLayout,
    Cell.add, Cell.scale]
  constructor <;> ring

/-- Any strict-inset owner route is strictly separated from a translated
coordinated variable fan when the two owner centers differ. -/
theorem insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_centers_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (firstCenter : Cell) (first : List Cell)
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell)
    (centersNe : firstCenter ≠
      Cell.add (placement.translation translate)
        (placement.position entry.1.1))
    (fanColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin firstCenter) first)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonVariableStub
          presentation entry fanColor)) := by
  exact insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
    firstBounded
    (fun point pointMember =>
      translatedOccurrenceCoordinatedRibbonVariableStub_points_bounded
        presentation compatible entry fanColor translate pointMember)
    centersNe

/-- Any strict-inset owner route is strictly separated from a translated
coordinated clause fan when the two owner centers differ. -/
theorem insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_centers_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (firstCenter : Cell) (first : List Cell)
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell)
    (centersNe : firstCenter ≠
      Cell.add (placement.translation translate)
        (occurrenceSourceClauseTarget presentation entry))
    (fanColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin firstCenter) first)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation entry fanColor)) := by
  exact insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
    firstBounded
    (fun point pointMember =>
      translatedOccurrenceCoordinatedRibbonClauseStub_points_bounded
        presentation compatible entry fanColor translate pointMember)
    centersNe

/-- Every checked clause core avoids a coordinated clause fan after an
arbitrary relative period translation.  A coincident lifted center uses the
finite local fan/core certificate; distinct centers are strictly separated. -/
theorem constructedClauseRoute_avoids_translatedOccurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (fanColor : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor))
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation entry fanColor)) := by
  let firstCenter := positionedClausePositionAt source clauseIndex
  let baseCenter := occurrenceSourceClauseTarget presentation entry
  let secondCenter := Cell.add (placement.translation translate) baseCenter
  by_cases centersEq : firstCenter = secondCenter
  · let entryClauseIndex :=
      occurrenceClauseIndex source.erase entry.1.1 entry.1.2
    let data := sourceClauseRibbonFanData presentation entryClauseIndex
    let group := occurrenceClauseTerminalGroup source.erase entry
    let lane := routedRibbonLane source.erase entry fanColor
    have active : data.GroupActive group :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        presentation entryClauseIndex entry
        entry.mem_activeClauseOccurrenceEntries
    have localAvoid := routesAvoidEachOther_comm
      (data.coordinatedRoute_avoids_clauseCore
        (compatible.2 entry) group active lane set coreColor)
    have translatedAvoid := routesAvoidEachOther_translate localAvoid
      (ribbonMacrocellOrigin secondCenter)
    have coreTranslation :
        translatePolyline (ribbonMacrocellOrigin secondCenter)
            (translatePolyline standardThreeStrandLayout.clauseOffset
              (X3CClauseOrthogonal.route set coreColor)) =
          translatePolyline
            (constructedClauseOrigin source standardThreeStrandLayout
              clauseIndex)
            (X3CClauseOrthogonal.route set coreColor) := by
      rw [translatePolyline_add]
      congr 1
      simp [constructedClauseOrigin, firstCenter, centersEq,
        ribbonMacrocellOrigin, Cell.add, add_comm]
    have fanTranslation :
        translatePolyline (ribbonMacrocellOrigin secondCenter)
            (data.coordinatedRoute group lane) =
          translatePolyline
            (ribbonMacrocellOrigin (placement.translation translate))
            (occurrenceCoordinatedRibbonClauseStub
              presentation entry fanColor) := by
      change translatePolyline (ribbonMacrocellOrigin secondCenter)
          (data.coordinatedRoute group lane) =
        translatePolyline (ribbonMacrocellOrigin
          (placement.translation translate))
          (translatePolyline (ribbonMacrocellOrigin baseCenter)
            (data.coordinatedRoute group lane))
      rw [translatePolyline_add]
      congr 1
      rw [show secondCenter =
          Cell.add baseCenter (placement.translation translate) by
        simp [secondCenter, Cell.add, add_comm]]
      exact ribbonMacrocellOrigin_add
        baseCenter (placement.translation translate)
    change RoutesAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set coreColor)))
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (data.coordinatedRoute group lane)) at translatedAvoid
    rw [coreTranslation, fanTranslation] at translatedAvoid
    exact translatedAvoid
  · have separated :=
      insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_centers_ne
        presentation compatible firstCenter
        (translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set coreColor))
        (all_clauseRoute_points_in_inset_rectangle set coreColor)
        entry translate centersEq fanColor
    rw [translatePolyline_add] at separated
    simpa [constructedClauseOrigin, firstCenter,
      ribbonMacrocellOrigin, Cell.add, add_comm] using
      separated.toRoutesAvoidEachOther

/-- Every listed contact of a translated coordinated clause stub with a
checked clause core occurs at the stub's outer tail. -/
theorem translatedOccurrenceCoordinatedRibbonClauseStub_meets_constructedClauseRoute_onlyAtFirstTail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (fanColor : WireColor) :
    RoutesMeetOnlyAtFirstTail
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation entry fanColor))
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor)) := by
  let firstCenter := positionedClausePositionAt source clauseIndex
  let baseCenter := occurrenceSourceClauseTarget presentation entry
  let secondCenter := Cell.add (placement.translation translate) baseCenter
  by_cases centersEq : firstCenter = secondCenter
  · let entryClauseIndex :=
      occurrenceClauseIndex source.erase entry.1.1 entry.1.2
    let data := sourceClauseRibbonFanData presentation entryClauseIndex
    let group := occurrenceClauseTerminalGroup source.erase entry
    let lane := routedRibbonLane source.erase entry fanColor
    have active : data.GroupActive group :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        presentation entryClauseIndex entry
        entry.mem_activeClauseOccurrenceEntries
    have localContacts :=
      coordinatedClauseRoute_meets_clauseCore_onlyAtFirstTail
        data (compatible.2 entry) group active lane set coreColor
    have translatedContacts := localContacts.translate
      (ribbonMacrocellOrigin secondCenter)
    have coreTranslation :
        translatePolyline (ribbonMacrocellOrigin secondCenter)
            (translatePolyline standardThreeStrandLayout.clauseOffset
              (X3CClauseOrthogonal.route set coreColor)) =
          translatePolyline
            (constructedClauseOrigin source standardThreeStrandLayout
              clauseIndex)
            (X3CClauseOrthogonal.route set coreColor) := by
      rw [translatePolyline_add]
      congr 1
      simp [constructedClauseOrigin, firstCenter, centersEq,
        ribbonMacrocellOrigin, Cell.add, add_comm]
    have fanTranslation :
        translatePolyline (ribbonMacrocellOrigin secondCenter)
            (data.coordinatedRoute group lane) =
          translatePolyline
            (ribbonMacrocellOrigin (placement.translation translate))
            (occurrenceCoordinatedRibbonClauseStub
              presentation entry fanColor) := by
      change translatePolyline (ribbonMacrocellOrigin secondCenter)
          (data.coordinatedRoute group lane) =
        translatePolyline (ribbonMacrocellOrigin
          (placement.translation translate))
          (translatePolyline (ribbonMacrocellOrigin baseCenter)
            (data.coordinatedRoute group lane))
      rw [translatePolyline_add]
      congr 1
      rw [show secondCenter =
          Cell.add baseCenter (placement.translation translate) by
        simp [secondCenter, Cell.add, add_comm]]
      exact ribbonMacrocellOrigin_add
        baseCenter (placement.translation translate)
    change RoutesMeetOnlyAtFirstTail
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (data.coordinatedRoute group lane))
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set coreColor))) at translatedContacts
    rw [fanTranslation, coreTranslation] at translatedContacts
    exact translatedContacts
  · have separated :=
      insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_centers_ne
        presentation compatible firstCenter
        (translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set coreColor))
        (all_clauseRoute_points_in_inset_rectangle set coreColor)
        entry translate centersEq fanColor
    rw [translatePolyline_add] at separated
    apply RoutesMeetOnlyAtFirstTail.of_strict
    exact (by
      simpa [constructedClauseOrigin, firstCenter,
        ribbonMacrocellOrigin, Cell.add, add_comm] using separated.symm)

/-- Every assembled finite incidence core is strictly separated from every
nonzero-translated coordinated variable fan. -/
theorem assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (fanColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation entry fanColor)) := by
  dsimp only
  let owner := tripleMacrocellOwner coreTriple.1
  let center := assemblyMacrocellOwnerPosition source placement owner
  rcases assembledTypedIncidenceCoreRoute_eq_ownerInsetRoute
      presentation width compatible coreTriple coreColor with
    ⟨localRoute, localBounded, coreEq⟩
  have ownerDeclared : owner.IsDeclared source.erase :=
    tripleMacrocellOwner_declared source.erase coreTriple.1 coreTriple.2
  have entryDeclared :
      (AssemblyMacrocellOwner.atom entry.1.1).IsDeclared source.erase :=
    entry.atom_mem
  have centersNe : center ≠
      Cell.add (placement.translation translate)
        (placement.position entry.1.1) := by
    exact assemblyMacrocellOwnerPosition_ne_translated_of_nonzero
      presentation.toPlanarIncidencePresentation anchorsZero
      owner (.atom entry.1.1) ownerDeclared entryDeclared
      translate translateNonzero
  have separated :=
    insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonVariableStub_of_centers_ne
      presentation.toPlanarIncidencePresentation compatible center
      localRoute localBounded entry translate centersNe fanColor
  rw [coreEq]
  simpa [center, owner] using separated

/-- Every assembled finite incidence core avoids every translated
coordinated clause fan.  Only a common clause port can remain as an outer
endpoint contact. -/
theorem assembledTypedIncidenceCoreRoute_avoids_translatedOccurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (fanColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry fanColor)) := by
  dsimp only
  let planar := presentation.toPlanarIncidencePresentation
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  rcases coreTriple with ⟨coreTriple, coreMember⟩
  cases coreTriple with
  | ordinary atom slot variant localTriple =>
      let location := ordinaryTriple_location source.erase
        atom slot variant localTriple coreMember
      let owner : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      let localRoute :=
        translatePolyline standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source.erase atom).route
            (activeVariableSiteTriple source.erase atom location.1
              slot location.2.1
              (.ordinary atom slot variant localTriple) location.2.2)
            coreColor)
      have centersNe :=
        occurrenceSourceVariablePosition_ne_translatedClauseTarget
          presentation owner entry translate
      have separated :=
        insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_centers_ne
          planar compatible (placement.position atom) localRoute
          (sourceVariableSiteRoute_points_in_inset_rectangle
            source.erase atom location.1 _ coreColor)
          entry translate (by simpa [owner] using centersNe) fanColor
      exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
        simpa [assembledTypedIncidenceCoreRoute, assembledOrdinaryPrefix,
          typedVariableSiteRoute, localRoute, location, routing,
          coordinatedSourceRibbonThreeStrandRouting,
          RibbonEndpointFanSystem.threeStrandRouting,
          constructedVariableOrigin, ribbonMacrocellOrigin,
          translatePolyline_add, Cell.add, add_comm] using separated)
  | fixedRed atom slot localTriple =>
      let location := fixedRedTriple_location source.erase
        atom slot localTriple coreMember
      let owner : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      let localRoute :=
        translatePolyline standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source.erase atom).route
            (activeVariableSiteTriple source.erase atom location.1
              slot location.2.1
              (.fixedRed atom slot localTriple) location.2.2)
            coreColor)
      have centersNe :=
        occurrenceSourceVariablePosition_ne_translatedClauseTarget
          presentation owner entry translate
      have separated :=
        insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_centers_ne
          planar compatible (placement.position atom) localRoute
          (sourceVariableSiteRoute_points_in_inset_rectangle
            source.erase atom location.1 _ coreColor)
          entry translate (by simpa [owner] using centersNe) fanColor
      exact RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther (by
        simpa [assembledTypedIncidenceCoreRoute, assembledFixedRedPrefix,
          typedVariableSiteRoute, localRoute, location, routing,
          coordinatedSourceRibbonThreeStrandRouting,
          RibbonEndpointFanSystem.threeStrandRouting,
          constructedVariableOrigin, ribbonMacrocellOrigin,
          translatePolyline_add, Cell.add, add_comm] using separated)
  | clause clauseIndex set =>
      simpa [assembledTypedIncidenceCoreRoute, routing,
        assembledClauseRoute, orientedIncidenceLocalRoute,
        coordinatedSourceRibbonThreeStrandRouting,
        RibbonEndpointFanSystem.threeStrandRouting] using
        constructedClauseRoute_avoids_translatedOccurrenceCoordinatedRibbonClauseStub
          planar compatible clauseIndex set coreColor entry translate fanColor

/-- A variable-owned finite core is strictly separated from every translated
coordinated clause fan. -/
theorem assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_atom_owner
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (fanColor : WireColor)
    (atomOwner :
      ∃ atom, tripleMacrocellOwner coreTriple.1 = .atom atom) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry fanColor)) := by
  dsimp only
  let planar := presentation.toPlanarIncidencePresentation
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  rcases coreTriple with ⟨coreTriple, coreMember⟩
  cases coreTriple with
  | ordinary atom slot variant localTriple =>
      let location := ordinaryTriple_location source.erase
        atom slot variant localTriple coreMember
      let owner : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      let localRoute :=
        translatePolyline standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source.erase atom).route
            (activeVariableSiteTriple source.erase atom location.1
              slot location.2.1
              (.ordinary atom slot variant localTriple) location.2.2)
            coreColor)
      have centersNe :=
        occurrenceSourceVariablePosition_ne_translatedClauseTarget
          presentation owner entry translate
      have separated :=
        insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_centers_ne
          planar compatible (placement.position atom) localRoute
          (sourceVariableSiteRoute_points_in_inset_rectangle
            source.erase atom location.1 _ coreColor)
          entry translate (by simpa [owner] using centersNe) fanColor
      simpa [assembledTypedIncidenceCoreRoute, assembledOrdinaryPrefix,
        typedVariableSiteRoute, localRoute, location, routing,
        coordinatedSourceRibbonThreeStrandRouting,
        RibbonEndpointFanSystem.threeStrandRouting,
        constructedVariableOrigin, ribbonMacrocellOrigin,
        translatePolyline_add, Cell.add, add_comm] using separated
  | fixedRed atom slot localTriple =>
      let location := fixedRedTriple_location source.erase
        atom slot localTriple coreMember
      let owner : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      let localRoute :=
        translatePolyline standardThreeStrandLayout.variableOffset
          ((sourceVariableSiteDrawing source.erase atom).route
            (activeVariableSiteTriple source.erase atom location.1
              slot location.2.1
              (.fixedRed atom slot localTriple) location.2.2)
            coreColor)
      have centersNe :=
        occurrenceSourceVariablePosition_ne_translatedClauseTarget
          presentation owner entry translate
      have separated :=
        insetRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_centers_ne
          planar compatible (placement.position atom) localRoute
          (sourceVariableSiteRoute_points_in_inset_rectangle
            source.erase atom location.1 _ coreColor)
          entry translate (by simpa [owner] using centersNe) fanColor
      simpa [assembledTypedIncidenceCoreRoute, assembledFixedRedPrefix,
        typedVariableSiteRoute, localRoute, location, routing,
        coordinatedSourceRibbonThreeStrandRouting,
        RibbonEndpointFanSystem.threeStrandRouting,
        constructedVariableOrigin, ribbonMacrocellOrigin,
        translatePolyline_add, Cell.add, add_comm] using separated
  | clause clauseIndex set =>
      rcases atomOwner with ⟨atom, ownerEq⟩
      simp [tripleMacrocellOwner] at ownerEq

/-- For every core and translated clause fan, all possible listed contact is
at the fan's outer tail. -/
theorem translatedOccurrenceCoordinatedRibbonClauseStub_meets_assembledTypedIncidenceCoreRoute_onlyAtFirstTail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (coreTriple :
      {triple : Triple Variable // triple ∈ triples source.erase})
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (fanColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesMeetOnlyAtFirstTail
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry fanColor))
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor) := by
  dsimp only
  let planar := presentation.toPlanarIncidencePresentation
  let routing := coordinatedSourceRibbonThreeStrandRouting
    presentation width compatible
  rcases coreTriple with ⟨coreTriple, coreMember⟩
  cases coreTriple with
  | ordinary atom slot variant localTriple =>
      apply RoutesMeetOnlyAtFirstTail.of_strict
      exact
        (assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_atom_owner
          presentation width compatible
          ⟨.ordinary atom slot variant localTriple, coreMember⟩
          coreColor entry translate fanColor ⟨atom, rfl⟩).symm
  | fixedRed atom slot localTriple =>
      apply RoutesMeetOnlyAtFirstTail.of_strict
      exact
        (assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_atom_owner
          presentation width compatible
          ⟨.fixedRed atom slot localTriple, coreMember⟩
          coreColor entry translate fanColor ⟨atom, rfl⟩).symm
  | clause clauseIndex set =>
      simpa [assembledTypedIncidenceCoreRoute, routing,
        assembledClauseRoute, orientedIncidenceLocalRoute,
        coordinatedSourceRibbonThreeStrandRouting,
        RibbonEndpointFanSystem.threeStrandRouting] using
        translatedOccurrenceCoordinatedRibbonClauseStub_meets_constructedClauseRoute_onlyAtFirstTail
          planar compatible clauseIndex set coreColor entry translate fanColor

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
