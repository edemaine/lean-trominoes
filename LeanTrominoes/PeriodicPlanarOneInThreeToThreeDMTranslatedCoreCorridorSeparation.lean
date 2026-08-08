import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedCoreSeparation

/-!
# Separation of finite incidence cores from translated corridors

Every finite incidence core lies in the strict inset of its source-owner
macrocell.  A source occurrence route covering that owner makes its center
an endpoint of one lifted route.  Endpoint-only contact between distinct
lifted routes then keeps that center out of every nonzero-translated
corridor interior.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A declared incidence-core owner is an endpoint of some active unit
source route. -/
theorem assembledTypedIncidenceCoreOwner_exists_endpointRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (triple : {triple : Triple Variable // triple ∈ triples source.erase}) :
    ∃ entry : ActiveOccurrenceEntry source.erase,
      RoutePointIsEndpoint
        (occurrenceUnitSourceRoute presentation entry)
        (assemblyMacrocellOwnerPosition source placement
          (tripleMacrocellOwner triple.1)) := by
  rcases triple with ⟨triple, tripleMember⟩
  cases triple with
  | ordinary atom slot variant localTriple =>
      let location := ordinaryTriple_location source.erase
        atom slot variant localTriple tripleMember
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      refine ⟨entry, Or.inl ?_⟩
      simpa [entry, assemblyMacrocellOwnerPosition,
        tripleMacrocellOwner] using
        occurrenceUnitSourceRoute_variableEndpoint_head?
          presentation entry
  | fixedRed atom slot localTriple =>
      let location := fixedRedTriple_location source.erase
        atom slot localTriple tripleMember
      let entry : ActiveOccurrenceEntry source.erase :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source.erase atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      refine ⟨entry, Or.inl ?_⟩
      simpa [entry, assemblyMacrocellOwnerPosition,
        tripleMacrocellOwner] using
        occurrenceUnitSourceRoute_variableEndpoint_head?
          presentation entry
  | clause clauseIndex set =>
      have declared := tripleMacrocellOwner_declared source.erase
        (.clause clauseIndex set) tripleMember
      have indexLt : clauseIndex < source.clauses.length := by
        simpa [tripleMacrocellOwner,
          AssemblyMacrocellOwner.IsDeclared,
          PositionedPeriodicCNF.erase] using declared
      rcases exists_occurrenceUnitSourceRoute_ending_at_clauseCenter
          presentation anchorsZero occurrences arity clauseIndex indexLt with
        ⟨entry, endpoint⟩
      refine ⟨entry, Or.inr ?_⟩
      simpa [assemblyMacrocellOwnerPosition,
        tripleMacrocellOwner] using endpoint

/-- An owner center covered by one unshifted source route cannot occur as an
interior center of a source route at a nonzero relative period shift. -/
theorem assemblyMacrocellOwnerPosition_not_mem_translatedOccurrenceUnitSourceRoute_tail_dropLast
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (owner : AssemblyMacrocellOwner Variable)
    (covering entry : ActiveOccurrenceEntry source.erase)
    (coveringEndpoint :
      RoutePointIsEndpoint
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation covering)
        (assemblyMacrocellOwnerPosition source placement owner))
    (translate : Cell) (translateNonzero : translate ≠ (0, 0)) :
    assemblyMacrocellOwnerPosition source placement owner ∉
      (translatePolyline (placement.translation translate)
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry)).tail.dropLast := by
  let planar := presentation.toPlanarIncidencePresentation
  let coveringRoute := occurrenceUnitSourceRoute planar covering
  let translatedRoute :=
    translatePolyline (placement.translation translate)
      (occurrenceUnitSourceRoute planar entry)
  let center := assemblyMacrocellOwnerPosition source placement owner
  intro centerMember
  have translatedNodup : translatedRoute.Nodup := by
    simpa [translatedRoute, planar] using
      translatedOccurrenceUnitSourceRoute_nodup
        presentation entry translate
  have centerNotEndpoint :
      ¬RoutePointIsEndpoint translatedRoute center :=
    not_routePointIsEndpoint_of_mem_tail_dropLast_of_nodup
      translatedNodup (by simpa [translatedRoute, center] using centerMember)
  have meetOnly : RoutesMeetOnlyAtEndpoints coveringRoute translatedRoute := by
    simpa [coveringRoute, translatedRoute, planar,
      PeriodicVariablePlacement.translation, Cell.scale] using
      translatedOccurrenceUnitSourceRoutes_meetOnlyAtEndpoints
        presentation covering entry (0, 0) translate
          (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
            planar covering entry translateNonzero)
  have coveringMember : center ∈ coveringRoute := by
    rcases coveringEndpoint with head | last
    · exact List.mem_of_mem_head? (by simpa [coveringRoute, center, planar] using head)
    · exact mem_of_getLast?_eq_some (by simpa [coveringRoute, center, planar] using last)
  have translatedMember : center ∈ translatedRoute := by
    apply List.mem_of_mem_tail
    exact List.mem_of_mem_dropLast
      (by simpa [translatedRoute, center] using centerMember)
  rcases List.mem_iff_get.mp coveringMember with
    ⟨coveringIndex, coveringPointEq⟩
  rcases List.mem_iff_get.mp translatedMember with
    ⟨translatedIndex, translatedPointEq⟩
  have endpoints := meetOnly coveringIndex translatedIndex
    (coveringPointEq.trans translatedPointEq.symm)
  apply centerNotEndpoint
  have endpointAtIndex :
      RoutePointIsEndpoint translatedRoute
        (translatedRoute.get translatedIndex) := endpoints.2
  rw [translatedPointEq] at endpointAtIndex
  exact endpointAtIndex

/-- A strict-inset route whose center is fresh from the translated source
route interior strictly avoids the corresponding translated ribbon
corridor. -/
theorem insetRoute_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (firstCenter : Cell) (first : List Cell)
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell)
    (interiorFresh :
      firstCenter ∉
        (translatePolyline (placement.translation translate)
          (occurrenceUnitSourceRoute
            presentation.toPlanarIncidencePresentation entry)).tail.dropLast)
    (corridorColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin firstCenter) first)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry corridorColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := translatePolyline (placement.translation translate)
    (occurrenceUnitSourceRoute planar entry)
  have routeLength : 2 ≤ route.length := by
    simpa [route, translatePolyline] using
      occurrenceUnitSourceRoute_length planar entry
  change RoutesStrictlyAvoidEachOther _
    (translatePolyline
      (ribbonMacrocellOrigin (placement.translation translate))
      (ribbonCorridorCore
        (routedRibbonLane source.erase entry corridorColor)
        (occurrenceUnitSourceRoute planar entry)))
  rw [← ribbonCorridorCore_translatePolyline]
  change RoutesStrictlyAvoidEachOther _
    (ribbonCorridorCore
      (routedRibbonLane source.erase entry corridorColor) route)
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons start tail =>
      cases tail with
      | nil => simp [routeEquation] at routeLength
      | cons second rest =>
          have actualRouteEquation :
              route = start :: second :: rest := by
            simpa using routeEquation
          cases rest with
          | nil =>
              have pairRouteEquation : route = [start, second] := by
                simpa using actualRouteEquation
              have unitStep :
                  AxisDirection.IsUnitAxisStep start second := by
                have steps := translatedOccurrenceUnitSourceRoute_unitSteps
                  planar entry translate
                simpa [route, pairRouteEquation] using steps
              by_cases centerEq : firstCenter = start
              · have centersNe : firstCenter ≠ second := by
                  rw [centerEq]
                  exact unitStep.ne
                have separated :=
                  insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
                    (firstCenter := firstCenter) (secondCenter := second)
                    (second := ribbonCorridorCore
                      (routedRibbonLane source.erase entry corridorColor)
                      route)
                    firstBounded
                    (fun point pointMember => by
                      rw [pairRouteEquation] at pointMember
                      simp only [ribbonCorridorCore_pair,
                        List.mem_singleton] at pointMember
                      subst point
                      unfold ribbonCorridorCoreStart
                      rw [ribbonMacrocellExit_eq_entry_of_unitAxisStep
                        unitStep]
                      apply inRibbonMacrocell_add_origin
                      exact standardRibbonMacrocellEntry_bounded
                        (AxisDirection.between start second)
                        (routedRibbonLane source.erase entry corridorColor))
                    centersNe
                simpa [pairRouteEquation] using separated
              · have separated :=
                  insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
                    (firstCenter := firstCenter) (secondCenter := start)
                    (second := ribbonCorridorCore
                      (routedRibbonLane source.erase entry corridorColor)
                      route)
                    firstBounded
                    (fun point pointMember => by
                      rw [pairRouteEquation] at pointMember
                      simp only [ribbonCorridorCore_pair,
                        List.mem_singleton] at pointMember
                      subst point
                      exact ribbonMacrocellExit_bounded start
                        (AxisDirection.between start second)
                        (routedRibbonLane source.erase entry corridorColor))
                    centerEq
                simpa [pairRouteEquation] using separated
          | cons third rest =>
              have longRouteEquation :
                  route = start :: second :: third :: rest := by
                simpa using actualRouteEquation
              have unitSteps :
                  (start :: second :: third :: rest).IsChain
                    AxisDirection.IsUnitAxisStep := by
                rw [← longRouteEquation]
                simpa [route, planar] using
                  translatedOccurrenceUnitSourceRoute_unitSteps
                    planar entry translate
              have noReversal :
                  SourceRouteHasNoImmediateReversal
                    (start :: second :: third :: rest) := by
                rw [← longRouteEquation]
                simpa [route, planar] using
                  translatedOccurrenceUnitSourceRoute_hasNoImmediateReversal
                    presentation entry translate
              have fresh :
                  firstCenter ∉ (second :: third :: rest).dropLast := by
                change firstCenter ∉ route.tail.dropLast at interiorFresh
                rw [longRouteEquation] at interiorFresh
                simpa using interiorFresh
              exact
                translatedInsetRoute_strictlyAvoids_ribbonCorridorCore_of_interior_fresh
                  firstBounded start second third rest unitSteps noReversal
                  fresh (routedRibbonLane source.erase entry corridorColor)

/-- Every assembled finite incidence core strictly avoids every nonzero
period translate of every occurrence corridor. -/
theorem assembledTypedIncidenceCoreRoute_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
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
    (corridorColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledTypedIncidenceCoreRoute routing coreTriple coreColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry corridorColor)) := by
  dsimp only
  let owner := tripleMacrocellOwner coreTriple.1
  let center := assemblyMacrocellOwnerPosition source placement owner
  rcases assembledTypedIncidenceCoreRoute_eq_ownerInsetRoute
      presentation width compatible coreTriple coreColor with
    ⟨localRoute, localBounded, coreEq⟩
  rcases assembledTypedIncidenceCoreOwner_exists_endpointRoute
      presentation.toPlanarIncidencePresentation anchorsZero occurrences
        arity coreTriple with
    ⟨covering, coveringEndpoint⟩
  have fresh :
      center ∉
        (translatePolyline (placement.translation translate)
          (occurrenceUnitSourceRoute
            presentation.toPlanarIncidencePresentation entry)).tail.dropLast :=
    assemblyMacrocellOwnerPosition_not_mem_translatedOccurrenceUnitSourceRoute_tail_dropLast
      presentation owner covering entry
      (by simpa [center, owner] using coveringEndpoint)
      translate translateNonzero
  have separated :=
    insetRoute_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
      presentation center localRoute localBounded entry translate fresh
        corridorColor
  rw [coreEq]
  simpa [center, owner] using separated

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
