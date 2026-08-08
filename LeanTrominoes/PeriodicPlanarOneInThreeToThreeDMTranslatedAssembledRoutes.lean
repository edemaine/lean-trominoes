import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceAssembledRouteSeparation
import LeanTrominoes.RetainedRayRasterizationTranslation

/-!
# Translated assembled routes

The periodic lift compares a stored assembled route with physical-period
translates of another stored route.  This file exposes those translates in
the same component form used by the unshifted assembly: a finite variable or
clause core, optionally joined to a coordinated occurrence-route suffix.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PositionedPeriodicCNF

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Source planarity separates arbitrary additional lattice translates of
two rebased variable-to-clause routes whenever their resulting lifted-route
keys differ. -/
theorem PlanarIncidencePresentation.translatedVariableToClauseRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PlanarIncidencePresentation source placement)
    (continuous :
      (incidenceDrawing source placement
        presentation.routes).IsContinuouslyPlanar)
    (endpointContacts :
      (incidenceDrawing source placement presentation.routes)
        |>.RoutePointsMeetOnlyAtEndpoints)
    {first second : CNFIncidence Variable × Nat}
    (firstMember :
      first ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    (secondMember :
      second ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    (firstTranslate secondTranslate : Cell)
    (occurrencesDifferent :
      (first.2,
          Cell.add (variableToClauseTranslate first.1) firstTranslate) ≠
        (second.2,
          Cell.add (variableToClauseTranslate second.1) secondTranslate)) :
    RoutesAvoidEachOther
      (translatePolyline (placement.translation firstTranslate)
        (presentation.variableToClauseRoute first.1))
      (translatePolyline (placement.translation secondTranslate)
        (presentation.variableToClauseRoute second.1)) := by
  let drawing :=
    incidenceDrawing source placement presentation.routes
  have originalAvoid :=
    PeriodicGridDrawing.routeOccurrences_avoidEachOther
      (drawing := drawing)
      continuous endpointContacts
      (presentation.route_zipIdx_mem_of_tagged firstMember)
      (presentation.route_zipIdx_mem_of_tagged secondMember)
      (presentation.route_length_ge_two_of_tagged firstMember)
      (presentation.route_length_ge_two_of_tagged secondMember)
      (presentation.route_orthogonal_of_tagged firstMember)
      (presentation.route_orthogonal_of_tagged secondMember)
      (Cell.add (variableToClauseTranslate first.1) firstTranslate)
      (Cell.add (variableToClauseTranslate second.1) secondTranslate)
      occurrencesDifferent
  have reversed := routesAvoidEachOther_reverse originalAvoid
  have periodTranslationEq (offset : Cell) :
      drawing.periodTranslation offset =
        placement.translation offset := by
    unfold drawing PeriodicGridDrawing.periodTranslation
      PeriodicVariablePlacement.translation
    rw [incidenceDrawing_gridSize
      source placement presentation.routes
      presentation.periodPositive]
  unfold PlanarIncidencePresentation.variableToClauseRoute
  rw [translatePolyline_add, translatePolyline_add]
  simpa [variableToClauseTranslate, translatePolyline, List.map_reverse,
    periodTranslationEq, PeriodicVariablePlacement.translation_add] using
    reversed

end PositionedPeriodicCNF

namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Stable stored-route index selected for an active occurrence. -/
noncomputable def occurrenceSourceRouteIndex
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) : Nat :=
  (occurrenceSpliceData presentation entry).indexed.2

/-- The stable stored-route index determines the active variable/slot
entry. -/
theorem occurrenceSourceRouteIndex_injective
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement) :
    Function.Injective (occurrenceSourceRouteIndex presentation) := by
  intro first second indexEqual
  let firstData := occurrenceSpliceData presentation first
  let secondData := occurrenceSpliceData presentation second
  change firstData.indexed.2 = secondData.indexed.2 at indexEqual
  have firstAt := firstData.indexedMember
  have secondAt := secondData.indexedMember
  rw [List.mem_zipIdx_iff_getElem?] at firstAt secondAt
  have incidenceEqual :
      firstData.indexed.1 = secondData.indexed.1 := by
    rw [indexEqual] at firstAt
    exact Option.some.inj (firstAt.symm.trans secondAt)
  have taggedEqual : firstData.tagged = secondData.tagged := by
    calc
      firstData.tagged =
          incidenceTaggedOccurrence firstData.indexed.1 :=
        firstData.metadataEq.symm
      _ = incidenceTaggedOccurrence secondData.indexed.1 :=
        congrArg incidenceTaggedOccurrence incidenceEqual
      _ = secondData.tagged := secondData.metadataEq
  have firstAtom :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase first.1.1 first.1.2 firstData.tagged
      firstData.occurrenceLookup).2
  have secondAtom :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase second.1.1 second.1.2 secondData.tagged
      secondData.occurrenceLookup).2
  have atomEqual : first.1.1 = second.1.1 := by
    calc
      first.1.1 = firstData.tagged.1.atom := firstAtom.symm
      _ = secondData.tagged.1.atom :=
        congrArg (fun tagged => tagged.1.atom) taggedEqual
      _ = second.1.1 := secondAtom
  have firstLookup :
      occurrenceAt source.erase second.1.1 first.1.2 =
        some secondData.tagged := by
    simpa [atomEqual, taggedEqual] using firstData.occurrenceLookup
  have slotEqual : first.1.2 = second.1.2 :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_slot_unique
      source.erase second.1.1 secondData.tagged
      first.1.2 second.1.2 firstLookup secondData.occurrenceLookup
  apply Subtype.ext
  exact Prod.ext atomEqual slotEqual

/-- Lifted source-route identity after an additional semantic lattice
translation. -/
noncomputable def occurrenceSourceRouteKeyAt
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) : Nat × Cell :=
  let key := occurrenceSourceRouteKey presentation entry
  (key.1, Cell.add key.2 translate)

/-- A nonzero relative lattice translation makes the lifted source-route
key differ, even if the two finite active entries are the same. -/
theorem occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    {translate : Cell} (translateNonzero : translate ≠ (0, 0)) :
    occurrenceSourceRouteKeyAt presentation first (0, 0) ≠
      occurrenceSourceRouteKeyAt presentation second translate := by
  intro keysEqual
  have indicesEqual :
      occurrenceSourceRouteIndex presentation first =
        occurrenceSourceRouteIndex presentation second := by
    simpa [occurrenceSourceRouteKeyAt, occurrenceSourceRouteKey,
      occurrenceSourceRouteIndex] using congrArg Prod.fst keysEqual
  have entriesEqual :=
    occurrenceSourceRouteIndex_injective presentation indicesEqual
  subst second
  have translatesEqual : (0, 0) = translate := by
    apply Cell.add_left_injective
      (occurrenceSourceRouteKey presentation first).2
    simpa [occurrenceSourceRouteKeyAt] using congrArg Prod.snd keysEqual
  exact translateNonzero translatesEqual.symm

/-- Arbitrary additionally translated occurrence source routes inherit
complete separation from the continuously planar periodic source drawing. -/
theorem translatedOccurrenceSourceRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (firstTranslate secondTranslate : Cell)
    (different :
      occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation first firstTranslate ≠
        occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation second secondTranslate) :
    RoutesAvoidEachOther
      (translatePolyline (placement.translation firstTranslate)
        (occurrenceSourceRoute
          presentation.toPlanarIncidencePresentation first))
      (translatePolyline (placement.translation secondTranslate)
        (occurrenceSourceRoute
          presentation.toPlanarIncidencePresentation second)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstData := occurrenceSpliceData planar first
  let secondData := occurrenceSpliceData planar second
  exact
    planar.translatedVariableToClauseRoutes_avoidEachOther
      presentation.continuouslyPlanar presentation.endpointContacts
      firstData.indexedMember secondData.indexedMember
      firstTranslate secondTranslate
      (by
        simpa [occurrenceSourceRouteKeyAt, occurrenceSourceRouteKey,
          occurrenceSourceRouteIndex, planar, firstData, secondData] using
          different)

/-- Every source occurrence route avoids every nonzero relative lattice
translate of every source occurrence route. -/
theorem occurrenceSourceRoute_avoids_nonzeroTranslate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    {translate : Cell} (translateNonzero : translate ≠ (0, 0)) :
    RoutesAvoidEachOther
      (occurrenceSourceRoute
        presentation.toPlanarIncidencePresentation first)
      (translatePolyline (placement.translation translate)
        (occurrenceSourceRoute
          presentation.toPlanarIncidencePresentation second)) := by
  simpa [PeriodicVariablePlacement.translation, Cell.scale,
    translatePolyline_zero] using
    translatedOccurrenceSourceRoutes_avoidEachOther
      presentation first second (0, 0) translate
      (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
        presentation.toPlanarIncidencePresentation first second
        translateNonzero)

/-- Translating an assembled ordinary core adds the offset to its global
variable-site origin. -/
theorem translatePolyline_assembledOrdinaryPrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (offset : Cell)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor) :
    translatePolyline offset
        (assembledOrdinaryPrefix routing atom slot variant localTriple
          member color) =
      let location :=
        ordinaryTriple_location source atom slot variant localTriple member
      translatePolyline
        (Cell.add (routing.variableOrigin atom) offset)
        (typedVariableSiteRoute source atom location.1 slot location.2.1
          (.ordinary atom slot variant localTriple) location.2.2 color) := by
  simp [assembledOrdinaryPrefix, translatePolyline_add]

/-- Translating an assembled fixed-red core adds the offset to its global
variable-site origin. -/
theorem translatePolyline_assembledFixedRedPrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (offset : Cell)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor) :
    translatePolyline offset
        (assembledFixedRedPrefix routing atom slot localTriple member color) =
      let location :=
        fixedRedTriple_location source atom slot localTriple member
      translatePolyline
        (Cell.add (routing.variableOrigin atom) offset)
        (typedVariableSiteRoute source atom location.1 slot location.2.1
          (.fixedRed atom slot localTriple) location.2.2 color) := by
  simp [assembledFixedRedPrefix, translatePolyline_add]

/-- Translating an assembled clause core adds the offset to its global
clause origin. -/
theorem translatePolyline_assembledClauseRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (offset : Cell)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) :
    translatePolyline offset
        (assembledClauseRoute routing clauseIndex set color) =
      translatePolyline
        (Cell.add (routing.clauseOrigin clauseIndex) offset)
        (orientedIncidenceLocalRoute source
          (.clause clauseIndex set) color) := by
  simp [assembledClauseRoute, translatePolyline_add]

/-- Translation preserves the last endpoint of a route, adding the common
offset to that endpoint. -/
theorem translatePolyline_getLast?_eq_some
    (offset : Cell) (route : List Cell) (boundary : Cell)
    (last : route.getLast? = some boundary) :
    (translatePolyline offset route).getLast? =
      some (Cell.add offset boundary) := by
  simpa [translatePolyline, List.getLast?_map] using
    congrArg (Option.map (Cell.add offset)) last

/-- Translation preserves the first endpoint of a route, adding the common
offset to that endpoint. -/
theorem translatePolyline_head?_eq_some
    (offset : Cell) (route : List Cell) (boundary : Cell)
    (head : route.head? = some boundary) :
    (translatePolyline offset route).head? =
      some (Cell.add offset boundary) := by
  simpa [translatePolyline, List.head?_map] using
    congrArg (Option.map (Cell.add offset)) head

/-- A translated assembled typed incidence is either its translated core
alone or the translated core joined at the translated certified port to the
translated coordinated occurrence suffix. -/
theorem translatePolyline_assembledTypedIncidenceRoute_eq_core_or_join
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (offset : Cell)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) :
    translatePolyline offset
        (assembledTypedIncidenceRoute routing triple color) =
        translatePolyline offset
          (assembledTypedIncidenceCoreRoute routing triple color) ∨
      ∃ (entry : ActiveOccurrenceEntry source) (boundary : Cell),
        triple.1 =
            routedOccurrenceTriple source entry.1.1 entry.1.2 color ∧
          (translatePolyline offset
            (assembledTypedIncidenceCoreRoute routing triple color)).getLast? =
              some (Cell.add offset boundary) ∧
          (translatePolyline offset
            (routing.route entry color)).head? =
              some (Cell.add offset boundary) ∧
          translatePolyline offset
              (assembledTypedIncidenceRoute routing triple color) =
            joinAtEndpoint
              (translatePolyline offset
                (assembledTypedIncidenceCoreRoute routing triple color))
              (translatePolyline offset (routing.route entry color)) := by
  rcases assembledTypedIncidenceRoute_eq_core_or_join
      routing triple color with core | joined
  · exact Or.inl (congrArg (translatePolyline offset) core)
  · rcases joined with
      ⟨entry, boundary, tripleEq, coreLast, routeHead, routeEq⟩
    refine Or.inr ⟨entry, boundary, tripleEq, ?_, ?_, ?_⟩
    · exact translatePolyline_getLast?_eq_some
        offset _ boundary coreLast
    · exact translatePolyline_head?_eq_some
        offset _ boundary routeHead
    · rw [routeEq, translatePolyline_joinAtEndpoint]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
