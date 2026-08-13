/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation
import LeanTrominoes.RetainedFinalFlatNormalizedBoundary
import LeanTrominoes.OrthogonalPolylineLinearSeparation

/-!
# Routed-clause direct escapes at carrier boundaries

The routed-clause direct atlas has a deliberately wide customized escape,
so it does not fit the ordinary terminal transverse corridor.  It is still
deep inside the routed-clause macrocell, however.  This file expresses each
carrier boundary as an inward-facing linear half-plane and certifies that
every routed-clause escape lies strictly on its inside.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- Unit normal pointing from a carrier boundary into its macrocell. -/
def carrierBoundaryInwardNormal : CornerPort → Cell
  | .west => (1, 0)
  | .east => (-1, 0)
  | .south => (0, 1)
  | .north => (0, -1)

/-- The local boundary threshold after the source-clearance scaling and
the complete terminal-fan refinement. -/
def directRefinedCarrierBoundaryValue
    (port : CornerPort) : Int :=
  Cell.linearValue (carrierBoundaryInwardNormal port)
    (Cell.scale
      (retainedTerminalFanTotalRefinement * 4)
      port.position)

/-- The same inward-facing threshold for a macrocell at an arbitrary
unscaled origin. -/
def directRefinedCarrierBoundaryValueAt
    (port : CornerPort) (origin : Cell) : Int :=
  Cell.linearValue (carrierBoundaryInwardNormal port)
    (Cell.scale
      (retainedTerminalFanTotalRefinement * 4)
      (Cell.add origin port.position))

/-- Every point of every customized routed-clause escape is strictly inside
all four refined carrier half-planes of the local macrocell.  The final
application needs only the west, north, or east boundary selected by the
active routed-clause arm; the uniform statement simplifies transport. -/
theorem retainedDirectRoutedClauseFanEscapeAt_strictly_inside_carrierBoundary
    (port : CornerPort) :
    ∀ (index :
        Fin
          (retainedDirectSourcePrefixChoices
            RetainedDirectClauseKind.routedClause).length)
      (slot : RetainedTerminalSlot)
      (point : Cell),
      point ∈
          (retainedDirectSourceFanEscapeAt
            RetainedDirectClauseKind.routedClause
            index slot).route →
        directRefinedCarrierBoundaryValue port <
          Cell.linearValue (carrierBoundaryInwardNormal port) point := by
  cases port <;>
    native_decide

/-- A routed-clause terminal vector cannot occur in any other direct atlas
kind.  This finite uniqueness fact lets route equality recover the kind of
a checked final choice. -/
theorem
    retainedDirectSourceLocalRouteAt_kind_eq_routedClause_of_terminalVector_eq :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (routedIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            RetainedDirectClauseKind.routedClause).length),
      PeriodicThreeSATThree.routeTerminalVector
          (retainedDirectSourceLocalRouteAt kind index) =
        PeriodicThreeSATThree.routeTerminalVector
          (retainedDirectSourceLocalRouteAt
            RetainedDirectClauseKind.routedClause routedIndex) →
        kind = RetainedDirectClauseKind.routedClause := by
  native_decide

/-- Every routed-clause atlas incidence is genuinely oblique.  Thus the
exceptional wide escape never overlaps the aligned direct-source branch. -/
theorem retainedDirectRoutedClauseLocalSegment_not_axisAligned :
    ∀ (index :
        Fin
          (retainedDirectSourcePrefixChoices
            RetainedDirectClauseKind.routedClause).length),
      ¬(⟨(retainedDirectSourceLocalRouteAt
              RetainedDirectClauseKind.routedClause index).headD (0, 0),
            (retainedDirectSourceLocalRouteAt
              RetainedDirectClauseKind.routedClause index).getLastD
                (0, 0)⟩ : GridSegment).IsAxisAligned := by
  native_decide

/-- A positioned choice of routed-clause kind retains that obliqueness. -/
theorem RetainedDirectSourceRouteChoice.sourceSegment_not_axisAligned_of_kind_eq_routedClause
    (choice : RetainedDirectSourceRouteChoice)
    (kindEq : choice.kind = RetainedDirectClauseKind.routedClause) :
    ¬choice.sourceSegment.IsAxisAligned := by
  rcases choice with ⟨origin, kind, index⟩
  change kind = RetainedDirectClauseKind.routedClause at kindEq
  subst kind
  let localSegment : GridSegment :=
    ⟨(retainedDirectSourceLocalRouteAt
        RetainedDirectClauseKind.routedClause index).headD (0, 0),
      (retainedDirectSourceLocalRouteAt
        RetainedDirectClauseKind.routedClause index).getLastD (0, 0)⟩
  have localOblique :=
    retainedDirectRoutedClauseLocalSegment_not_axisAligned index
  intro positionedAligned
  apply localOblique
  exact
    (GridSegment.isAxisAligned_translate localSegment origin).mp
      (by
        simpa [RetainedDirectSourceRouteChoice.sourceSegment,
          localSegment, GridSegment.translate] using positionedAligned)

/-- A successful raw selector has routed-clause atlas kind exactly when its
metadata source is a routed clause. -/
theorem retainedDirectSourceRouteChoice?_kind_eq_routedClause_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source :
      PeriodicOrthocrossing.DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedDirectSourceRouteChoice? formula source literalIndex =
        some choice) :
    choice.kind = RetainedDirectClauseKind.routedClause ↔
      ∃ site, source =
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
          site := by
  cases source with
  | crossover crossing localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
      rcases lookup with ⟨localClauseIndexLt, literalIndexLt, rfl⟩
      simp
  | carrier link localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
  | bend bend localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
  | routedClause site =>
      simp [retainedDirectSourceRouteChoice?] at lookup
      rcases lookup with ⟨literalIndexLt, rfl⟩
      simp
  | routedVariable site armIndex arm link localClauseIndex =>
      simp [retainedDirectSourceRouteChoice?] at lookup
      rcases lookup with ⟨localClauseIndexLt, literalIndexLt, rfl⟩
      simp

/-- For a retained component, the selected incidence drawing exposes exactly
the source's unpositioned clause family. -/
theorem retainedComponentMember_incidenceDrawing_formula_eq_clauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (source :
      PeriodicOrthocrossing.DrawingPlanarSATClauseSource Variable)
    (sourceMember : source.RetainedComponentMember formula) :
    (source.incidenceDrawing formula).formula =
      source.clauseFormula formula := by
  cases source with
  | crossover crossing localClauseIndex =>
      simp [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing,
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.clauseFormula]
  | carrier link localClauseIndex =>
      simpa [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing,
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.clauseFormula] using
        PeriodicOrthocrossing.retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
          wellFormed degree isLocal sourceMember
  | bend bend localClauseIndex =>
      simp [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing,
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.clauseFormula,
        PeriodicOrthocrossing.drawingPlanarSATBendCornerIncidenceDrawing_formula]
  | routedClause site =>
      simp [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing,
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.clauseFormula]
  | routedVariable site armIndex arm link localClauseIndex =>
      have linkMember :=
        List.fst_mem_of_mem_zipIdx sourceMember.2.1
      have armEq := sourceMember.2.2
      simpa [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing,
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.clauseFormula] using
        PeriodicOrthocrossing.drawingPlanarSATRoutedVariableIncidenceDrawing_formula
          formula site arm link linkMember armEq

/-- All three routed-clause local incidences start at their common clause
point. -/
theorem retainedDirectRoutedClauseLocalRouteAt_head? :
    ∀ (index :
      Fin
        (retainedDirectSourcePrefixChoices
          RetainedDirectClauseKind.routedClause).length),
      (retainedDirectSourceLocalRouteAt
        RetainedDirectClauseKind.routedClause index).head? =
        some (10, 10) := by
  native_decide

/-- Inverting a successful routed-clause lookup exposes the exact routed
atlas shape and its unscaled physical macrocell origin. -/
theorem retainedDirectSourceRouteChoice?_routedClause_eq_some_shape
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : PeriodicOrthocrossing.ClauseRouteSite)
    (literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (lookup :
      retainedDirectSourceRouteChoice?
          formula (.routedClause site) literalIndex =
        some choice) :
    ∃ index :
        Fin
          (retainedDirectSourcePrefixChoices
            RetainedDirectClauseKind.routedClause).length,
      choice = {
        origin := PeriodicOrthocrossing.routedClauseOrigin formula site
        kind := RetainedDirectClauseKind.routedClause
        index := index
      } := by
  simp only [retainedDirectSourceRouteChoice?] at lookup
  split at lookup
  next literalIndexLt =>
    simp only [Option.some.injEq] at lookup
    subst choice
    exact ⟨_, rfl⟩
  next =>
    contradiction

/-- Equality with a translated routed-clause local incidence recovers both
the routed-clause atlas kind and the physical macrocell origin of a checked
choice. -/
theorem
    RetainedDirectSourceRouteChoice.kind_origin_eq_routedClause_of_route_eq
    (choice : RetainedDirectSourceRouteChoice)
    (origin : Cell)
    (routedIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          RetainedDirectClauseKind.routedClause).length)
    (routeEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        PeriodicOrthocrossing.translatePolyline origin
          (retainedDirectSourceLocalRouteAt
            RetainedDirectClauseKind.routedClause routedIndex)) :
    choice.kind = RetainedDirectClauseKind.routedClause ∧
      choice.origin = origin := by
  rcases choice with ⟨choiceOrigin, kind, index⟩
  have vectorEq :=
    congrArg PeriodicThreeSATThree.routeTerminalVector routeEq
  rw [routeTerminalVector_translatePolyline,
    routeTerminalVector_translatePolyline] at vectorEq
  have kindEq :=
    retainedDirectSourceLocalRouteAt_kind_eq_routedClause_of_terminalVector_eq
      kind index routedIndex vectorEq
  subst kind
  refine ⟨rfl, ?_⟩
  have headEq := congrArg List.head? routeEq
  rw [PeriodicOrthocrossing.translatePolyline,
    PeriodicOrthocrossing.translatePolyline,
    List.head?_map, List.head?_map,
    retainedDirectRoutedClauseLocalRouteAt_head? index,
    retainedDirectRoutedClauseLocalRouteAt_head? routedIndex]
      at headEq
  simp only [Option.map_some, Option.some.injEq] at headEq
  rcases choiceOrigin with ⟨choiceX, choiceY⟩
  rcases origin with ⟨originX, originY⟩
  simp [Cell.add] at headEq
  change (choiceX, choiceY) = (originX, originY)
  apply Prod.ext <;> omega

/-- If the normalized source of a final flat route is a routed clause, any
checked choice representing that same route has routed-clause kind and the
normalized routed-clause macrocell origin. -/
theorem retainedFinalDirectChoice_kind_origin_eq_of_normalized_routedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    {macrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (site : PeriodicOrthocrossing.ClauseRouteSite)
    (sourceEq :
      normalized.source =
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
          site)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceRouteEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        taggedRoute.1) :
    choice.kind = RetainedDirectClauseKind.routedClause ∧
      choice.origin =
        PeriodicOrthocrossing.routedClauseOrigin formula site := by
  rcases normalized.exists_routeSelection
      formula wellFormed degree isLocal with
    ⟨selection⟩
  let selectedClause := selection.clause
  let selectedLiteral := selection.literal
  let selectedLiteralIndex := selection.literalIndex
  let metadata :
      PeriodicOrthocrossing.DrawingPlanarSATClauseMetadata Variable :=
    ⟨selectedClause, normalized.source⟩
  have drawingMember :
      (selectedClause, normalized.source.localClauseIndex) ∈
        (normalized.source.incidenceDrawing formula).formula.zipIdx := by
    simpa [selectedClause] using selection.clauseMember
  have clauseFormulaMember :
      (selectedClause, normalized.source.localClauseIndex) ∈
        (normalized.source.clauseFormula formula).zipIdx := by
    rw [sourceEq] at drawingMember ⊢
    simpa [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing,
      PeriodicOrthocrossing.DrawingPlanarSATClauseSource.localClauseIndex,
      PeriodicOrthocrossing.DrawingPlanarSATClauseSource.clauseFormula]
      using drawingMember
  have valid : metadata.RetainedValid formula := by
    apply
      (metadata.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mpr
    exact ⟨normalized.sourceMember, clauseFormulaMember⟩
  have routedValid :
      (⟨selectedClause,
          PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
            site⟩ :
        PeriodicOrthocrossing.DrawingPlanarSATClauseMetadata Variable)
          |>.RetainedValid formula := by
    simpa [metadata, sourceEq] using valid
  have selectedLiteralMember :
      (selectedLiteral, selectedLiteralIndex) ∈
        selectedClause.literals.zipIdx := by
    simpa [selectedLiteral, selectedLiteralIndex, selectedClause] using
      selection.literalMember
  rcases exists_retainedDirectSourceRouteChoice_routedClause
      formula selectedClause site routedValid
      selectedLiteralMember with
    ⟨rawChoice, rawLookup, _rawMatches⟩
  have rawRepresents :=
    retainedDirectSourceRouteChoice?_represents_of_eq_some
      formula
      (PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
        site)
      selectedLiteralIndex rawChoice rawLookup
  unfold RetainedDirectSourceRouteChoice.Represents at rawRepresents
  have selectionRouteEq :
      taggedRoute.1 =
        (normalized.source.incidenceDrawing formula).routes
          normalized.source.localClauseIndex selectedLiteralIndex := by
    simpa [selectedLiteralIndex] using selection.routeEq
  rw [sourceEq] at selectionRouteEq
  have rawRouteEq :
      PeriodicOrthocrossing.translatePolyline rawChoice.origin
          (retainedDirectSourceLocalRouteAt
            rawChoice.kind rawChoice.index) =
        taggedRoute.1 := by
    exact rawRepresents.trans selectionRouteEq.symm
  rcases retainedDirectSourceRouteChoice?_routedClause_eq_some_shape
      formula site selectedLiteralIndex rawChoice rawLookup with
    ⟨routedIndex, rawChoiceEq⟩
  subst rawChoice
  exact
    choice.kind_origin_eq_routedClause_of_route_eq
      (PeriodicOrthocrossing.routedClauseOrigin formula site)
      routedIndex
      (choiceRouteEq.trans rawRouteEq.symm)

/-- Conversely, a routed-clause atlas choice representing a normalized flat
macrocell route forces that normalized source itself to be a routed clause.
This recognizes the exceptional carrier-boundary case from the selected
route, without exposing its representative metadata. -/
theorem retainedFinalDirectChoice_exists_normalizedRoutedClause_of_kind_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (macrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute)
    (normalized :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (choice : RetainedDirectSourceRouteChoice)
    (kindEq : choice.kind = RetainedDirectClauseKind.routedClause)
    (choiceRouteEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        taggedRoute.1) :
    ∃ site : PeriodicOrthocrossing.ClauseRouteSite,
      normalized.source =
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
          site := by
  have localLength :=
    retainedDirectSourceLocalRouteAt_length choice.kind choice.index
  have routeLength : 2 ≤ taggedRoute.1.length := by
    rw [← choiceRouteEq]
    simp [PeriodicOrthocrossing.translatePolyline, localLength]
  have routeLast :
      taggedRoute.1.getLast? = some choice.sourceSegment.finish := by
    rcases List.length_eq_two.mp localLength with
      ⟨localHead, localLast, localRouteEq⟩
    rw [← choiceRouteEq]
    simp [localRouteEq, PeriodicOrthocrossing.translatePolyline,
      RetainedDirectSourceRouteChoice.sourceSegment]
  have finalSegmentEq :
      (⟨polylineLastEntrance taggedRoute.1,
          choice.sourceSegment.finish⟩ : GridSegment) =
        choice.sourceSegment := by
    rcases List.length_eq_two.mp localLength with
      ⟨localHead, localLast, localRouteEq⟩
    rw [← choiceRouteEq]
    simp [localRouteEq, PeriodicOrthocrossing.translatePolyline,
      polylineLastEntrance, polylineFirstExit,
      RetainedDirectSourceRouteChoice.sourceSegment]
  have choiceOblique :=
    choice.sourceSegment_not_axisAligned_of_kind_eq_routedClause kindEq
  have finalOblique :
      ¬(⟨polylineLastEntrance taggedRoute.1,
          choice.sourceSegment.finish⟩ : GridSegment).IsAxisAligned := by
    rw [finalSegmentEq]
    exact choiceOblique
  have componentDirect :=
    macrocell.component_isDirect_of_finalSegment_not_axisAligned
      formula wellFormed degree isLocal
      routeLength routeLast finalOblique
  have normalizedDirect :=
    normalized.componentIsDirect componentDirect
  rcases normalized.exists_routeSelection
      formula wellFormed degree isLocal with
    ⟨selection⟩
  let metadata :
      PeriodicOrthocrossing.DrawingPlanarSATClauseMetadata Variable :=
    ⟨selection.clause, normalized.source⟩
  have clauseFormulaMember :
      (selection.clause, normalized.source.localClauseIndex) ∈
        (normalized.source.clauseFormula formula).zipIdx := by
    rw [←
      retainedComponentMember_incidenceDrawing_formula_eq_clauseFormula
        formula wellFormed degree isLocal
        normalized.source normalized.sourceMember]
    exact selection.clauseMember
  have valid : metadata.RetainedValid formula := by
    apply
      (metadata.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mpr
    exact ⟨normalized.sourceMember, clauseFormulaMember⟩
  rcases
      LeanTrominoes.PeriodicEightOccurrenceSplit.DrawingPlanarSATClauseMetadata.exists_retainedDirectSourceRouteChoice
        metadata valid selection.literalMember
        (normalized.directCases normalizedDirect) with
    ⟨rawChoice, rawLookup, _rawMatches⟩
  have rawRepresents :=
    retainedDirectSourceRouteChoice?_represents_of_eq_some
      formula normalized.source selection.literalIndex
      rawChoice rawLookup
  unfold RetainedDirectSourceRouteChoice.Represents at rawRepresents
  have rawRouteEq :
      PeriodicOrthocrossing.translatePolyline rawChoice.origin
          (retainedDirectSourceLocalRouteAt
            rawChoice.kind rawChoice.index) =
        taggedRoute.1 :=
    rawRepresents.trans selection.routeEq.symm
  rcases choice with ⟨choiceOrigin, choiceKind, choiceIndex⟩
  change choiceKind = RetainedDirectClauseKind.routedClause at kindEq
  subst choiceKind
  have vectorEq :=
    congrArg PeriodicThreeSATThree.routeTerminalVector
      (rawRouteEq.trans choiceRouteEq.symm)
  rw [routeTerminalVector_translatePolyline,
    routeTerminalVector_translatePolyline] at vectorEq
  have rawKindEq :=
    retainedDirectSourceLocalRouteAt_kind_eq_routedClause_of_terminalVector_eq
      rawChoice.kind rawChoice.index choiceIndex vectorEq
  exact
    (retainedDirectSourceRouteChoice?_kind_eq_routedClause_iff
      formula normalized.source selection.literalIndex
      rawChoice rawLookup).mp rawKindEq

/-- A normalized carrier contact with a routed-clause source retains a
boundary whose origin is definitionally that routed clause's physical
macrocell origin.  This strengthens the generic boundary existence theorem
with the one equality needed by the positioned direct escape. -/
theorem retainedFinalRoutedClauseContact_exists_carrierBoundary_at_origin
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      PeriodicOrthocrossing.FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (normalized :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (site : PeriodicOrthocrossing.ClauseRouteSite)
    (sourceEq :
      normalized.source =
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
          site)
    (contact :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedCarrierContact
        formula carrier macrocell normalized) :
    ∃ boundary :
        PeriodicOrthocrossing.FinalGaugedFlatNormalizedCarrierBoundary
          carrierTaggedRoute.1 macrocellTaggedRoute.1,
      boundary.origin =
        PeriodicOrthocrossing.routedClauseOrigin formula site := by
  rcases carrier.exists_normalizedRouteSelection
      formula wellFormed degree isLocal with
    ⟨carrierClauseIndex, ⟨carrierSelection⟩⟩
  rcases normalized.exists_routeSelection
      formula wellFormed degree isLocal with
    ⟨macrocellSelection⟩
  have normalizedLinkMember :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  rcases contact with crossoverContact | terminalContact
  · rcases crossoverContact with
      ⟨crossing, localClauseIndex, crossingSourceEq, _incident⟩
    rw [sourceEq] at crossingSourceEq
    contradiction
  · rcases terminalContact with
      routedClauseContact | routedVariableContact
    · rcases routedClauseContact with
        ⟨contactSite, occurrence, contactSourceEq,
          occurrenceMember, incident⟩
      have siteEq : site = contactSite := by
        rw [sourceEq] at contactSourceEq
        injection contactSourceEq
      subst contactSite
      rcases incident with firstEqual | secondEqual
      · have interface :=
          PeriodicOrthocrossing.retainedDrawingCompleteCarrierLinkRaw_first_sourceTerminalInterface
            wellFormed degree isLocal normalizedLinkMember
            site occurrenceMember firstEqual
        have carrierBounded :=
          PeriodicOrthocrossing.retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst_of_raw
            wellFormed degree isLocal normalizedLinkMember
        rw [interface.1, interface.2] at carrierBounded
        have carrierBounded' :
            ((PeriodicOrthocrossing.DrawingPlanarSATClauseSource.carrier
              carrier.normalizedLink carrierClauseIndex).incidenceDrawing
                formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.OutsideCarrierBoundaryAt
                  (PeriodicOrthocrossing.routedClauseOrigin
                    formula site)) := by
          simpa [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing]
            using carrierBounded
        have macrocellBounded :
            (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.InsideCarrierBoundaryAt
                  (PeriodicOrthocrossing.routedClauseOrigin
                    formula site)) := by
          rw [sourceEq]
          exact
            PeriodicOrthocrossing.drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
              formula site
              (occurrence.sourceTerminal formula).duplicatorArm
        let boundary :=
          PeriodicOrthocrossing.FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
            carrierSelection macrocellSelection
            (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
            (PeriodicOrthocrossing.routedClauseOrigin formula site)
            carrierBounded' macrocellBounded
        exact ⟨boundary, rfl⟩
      · have interface :=
          PeriodicOrthocrossing.retainedDrawingCompleteCarrierLinkRaw_second_sourceTerminalInterface
            wellFormed degree isLocal normalizedLinkMember
            site occurrenceMember secondEqual
        have carrierBounded :=
          PeriodicOrthocrossing.retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond_of_raw
            wellFormed degree isLocal normalizedLinkMember
        rw [interface.1, interface.2] at carrierBounded
        have carrierBounded' :
            ((PeriodicOrthocrossing.DrawingPlanarSATClauseSource.carrier
              carrier.normalizedLink carrierClauseIndex).incidenceDrawing
                formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.OutsideCarrierBoundaryAt
                  (PeriodicOrthocrossing.routedClauseOrigin
                    formula site)) := by
          simpa [PeriodicOrthocrossing.DrawingPlanarSATClauseSource.incidenceDrawing]
            using carrierBounded
        have macrocellBounded :
            (normalized.source.incidenceDrawing formula).RoutePointsSatisfy
              ((occurrence.sourceTerminal formula).duplicatorArm.carrierPort
                |>.InsideCarrierBoundaryAt
                  (PeriodicOrthocrossing.routedClauseOrigin
                    formula site)) := by
          rw [sourceEq]
          exact
            PeriodicOrthocrossing.drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_insideCarrierBoundary
              formula site
              (occurrence.sourceTerminal formula).duplicatorArm
        let boundary :=
          PeriodicOrthocrossing.FinalGaugedFlatNormalizedCarrierBoundary.of_routeSelections
            carrierSelection macrocellSelection
            (occurrence.sourceTerminal formula).duplicatorArm.carrierPort
            (PeriodicOrthocrossing.routedClauseOrigin formula site)
            carrierBounded' macrocellBounded
        exact ⟨boundary, rfl⟩
    · rcases routedVariableContact with
        ⟨variableSite, armIndex, arm, link, localClauseIndex,
          occurrence, variableSourceEq, _occurrenceMember, _incident⟩
      rw [sourceEq] at variableSourceEq
      contradiction

/-- Scaling an outside carrier point by the construction's combined factor
places it on the closed outside of the refined linear threshold. -/
theorem linearValue_scale_le_directRefinedCarrierBoundaryValueAt_of_outside
    (port : CornerPort)
    (origin point : Cell)
    (outside : port.OutsideCarrierBoundaryAt origin point) :
    Cell.linearValue (carrierBoundaryInwardNormal port)
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          point) ≤
      directRefinedCarrierBoundaryValueAt port origin := by
  rcases origin with ⟨originX, originY⟩
  rcases point with ⟨pointX, pointY⟩
  cases port <;>
    simp [CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      carrierBoundaryInwardNormal,
      directRefinedCarrierBoundaryValueAt,
      retainedTerminalFanTotalRefinement_eq,
      CornerPort.position, Cell.linearValue,
      Cell.add, Cell.sub, Cell.scale] at outside ⊢ <;>
    omega

/-- Translating a routed-clause escape to its physical component origin
transports the strict local half-plane certificate to the refined absolute
carrier boundary. -/
theorem
    retainedDirectRoutedClausePositionedFanEscapeAt_strictly_inside_carrierBoundary
    (origin : Cell)
    (port : CornerPort)
    (index :
      Fin
        (retainedDirectSourcePrefixChoices
          RetainedDirectClauseKind.routedClause).length)
    (slot : RetainedTerminalSlot)
    {point : Cell}
    (pointMember :
      point ∈
        PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset origin)
          (retainedDirectSourceFanEscapeAt
            RetainedDirectClauseKind.routedClause
            index slot).route) :
    directRefinedCarrierBoundaryValueAt port origin <
      Cell.linearValue (carrierBoundaryInwardNormal port) point := by
  unfold PeriodicOrthocrossing.translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨localPoint, localPointMember, rfl⟩
  have localBound :=
    retainedDirectRoutedClauseFanEscapeAt_strictly_inside_carrierBoundary
      port index slot localPoint localPointMember
  rcases origin with ⟨originX, originY⟩
  rcases localPoint with ⟨pointX, pointY⟩
  cases port <;>
    simp [carrierBoundaryInwardNormal,
      directRefinedCarrierBoundaryValue,
      directRefinedCarrierBoundaryValueAt,
      retainedDirectSourceFanPositioningOffset,
      retainedTerminalFanTotalRefinement_eq,
      CornerPort.position, Cell.linearValue,
      Cell.add, Cell.scale] at localBound ⊢ <;>
    omega

/-- A source prefix on the carrier side is strictly separated from every
positioned routed-clause customized escape on the macrocell side. -/
theorem
    retainedScaledOutsidePrefix_strictlyAvoids_positionedRoutedClauseEscape
    (sourceRoute : List Cell)
    (origin : Cell)
    (port : CornerPort)
    (index :
      Fin
        (retainedDirectSourcePrefixChoices
          RetainedDirectClauseKind.routedClause).length)
    (slot : RetainedTerminalSlot)
    (sourceOutside :
      ∀ point ∈ sourceRoute.dropLast,
        port.OutsideCarrierBoundaryAt origin point) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset origin)
        (retainedDirectSourceFanEscapeAt
          RetainedDirectClauseKind.routedClause
          index slot).route) := by
  apply routesStrictlyAvoidEachOther_of_linear_separated
    (carrierBoundaryInwardNormal port)
    (directRefinedCarrierBoundaryValueAt port origin)
  · intro point pointMember
    unfold scalePolyline at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    exact
      linearValue_scale_le_directRefinedCarrierBoundaryValueAt_of_outside
        port origin sourcePoint
        (sourceOutside sourcePoint sourcePointMember)
  · intro point pointMember
    exact
      retainedDirectRoutedClausePositionedFanEscapeAt_strictly_inside_carrierBoundary
        origin port index slot pointMember

/-- The normalized routed-clause contact and checked-choice representation
discharge the origin and atlas-kind premises of the generic half-plane
separator. -/
theorem
    retainedFinalScaledCarrierPrefix_strictlyAvoids_routedClauseChoiceEscape
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      PeriodicOrthocrossing.FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (normalized :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (site : PeriodicOrthocrossing.ClauseRouteSite)
    (sourceEq :
      normalized.source =
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
          site)
    (contact :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedCarrierContact
        formula carrier macrocell normalized)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (choiceRouteEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        macrocellTaggedRoute.1) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        carrierTaggedRoute.1.dropLast)
      (PeriodicOrthocrossing.translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceFanEscapeAt
          choice.kind choice.index slot).route) := by
  have choiceData :=
    retainedFinalDirectChoice_kind_origin_eq_of_normalized_routedClause
      formula wellFormed degree isLocal normalized site sourceEq
      choice choiceRouteEq
  rcases
      retainedFinalRoutedClauseContact_exists_carrierBoundary_at_origin
        formula wellFormed degree isLocal
        carrier macrocell normalized site sourceEq contact with
    ⟨boundary, boundaryOriginEq⟩
  rcases choice with ⟨choiceOrigin, kind, index⟩
  rcases choiceData with ⟨kindEq, originEq⟩
  change kind = RetainedDirectClauseKind.routedClause at kindEq
  change choiceOrigin =
    PeriodicOrthocrossing.routedClauseOrigin formula site at originEq
  subst kind
  subst choiceOrigin
  apply
    retainedScaledOutsidePrefix_strictlyAvoids_positionedRoutedClauseEscape
      carrierTaggedRoute.1
      (PeriodicOrthocrossing.routedClauseOrigin formula site)
      boundary.port index slot
  intro point pointMember
  rw [← boundaryOriginEq]
  exact boundary.carrierOutside point
    (List.mem_of_mem_dropLast pointMember)

/-- Strict avoidance of a positioned direct escape and its fixed complete
tail assembles across their certified common checkpoint into strict
avoidance of the whole selected direct route. -/
theorem retainedSourcePrefix_strictlyAvoids_directCompleteRoute_of_pieces
    (sourcePrefix : List Cell)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (escapeAvoid :
      RoutesStrictlyAvoidEachOther
        sourcePrefix
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedDirectSourceFanEscapeAt
            choice.kind choice.index slot).route))
    (tailAvoid :
      RoutesStrictlyAvoidEachOther
        sourcePrefix
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedDirectSourceFanCompleteTailAt
            choice.kind choice.index slot))) :
    RoutesStrictlyAvoidEachOther
      sourcePrefix
      (choice.completeRoute slot) := by
  let offset :=
    retainedDirectSourceFanPositioningOffset choice.origin
  let boundary :=
    Cell.add offset
      (retainedTerminalFanOuterSourceEscapePoint
        (retainedDirectSourceFanCenterAt
          choice.kind choice.index)
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index)
        slot)
  have escapeLast :
      (PeriodicOrthocrossing.translatePolyline offset
        (retainedDirectSourceFanEscapeAt
          choice.kind choice.index slot).route).getLast? =
        some boundary := by
    have localLast :=
      (retainedDirectSourceFanEscapeAt
        choice.kind choice.index slot).last_eq
    simpa [PeriodicOrthocrossing.translatePolyline,
      List.getLast?_map, offset, boundary] using
      congrArg (Option.map (Cell.add offset)) localLast
  have tailHead :
      (PeriodicOrthocrossing.translatePolyline offset
        (retainedDirectSourceFanCompleteTailAt
          choice.kind choice.index slot)).head? =
        some boundary := by
    have localHead :=
      retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head?
        (retainedDirectSourceFanCenterAt
          choice.kind choice.index)
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index)
        slot
    simp [retainedDirectSourceFanCompleteTailAt,
      PeriodicOrthocrossing.translatePolyline,
      offset, boundary, localHead]
  unfold RetainedDirectSourceRouteChoice.completeRoute
    retainedDirectSourcePositionedFanCompleteRouteAt
  rw [retainedDirectSourceFanCompleteRouteAt,
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_eq_escape_join_tail,
    translatePolyline_joinAtEndpoint]
  exact escapeAvoid.join_right tailAvoid escapeLast tailHead

/-- At a normalized routed-clause/carrier contact, the half-plane escape
certificate and any certificate for the already-controlled post-escape tail
assemble into strict avoidance of the selected complete direct route. -/
theorem
    retainedFinalScaledCarrierPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      PeriodicOrthocrossing.FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (normalized :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    (site : PeriodicOrthocrossing.ClauseRouteSite)
    (sourceEq :
      normalized.source =
        PeriodicOrthocrossing.DrawingPlanarSATClauseSource.routedClause
          site)
    (contact :
      PeriodicOrthocrossing.FinalGaugedFlatNormalizedCarrierContact
        formula carrier macrocell normalized)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (choiceRouteEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        macrocellTaggedRoute.1)
    (tailAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline
          (retainedTerminalFanTotalRefinement * 4)
          carrierTaggedRoute.1.dropLast)
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedDirectSourceFanCompleteTailAt
            choice.kind choice.index slot))) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        carrierTaggedRoute.1.dropLast)
      (choice.completeRoute slot) := by
  apply retainedSourcePrefix_strictlyAvoids_directCompleteRoute_of_pieces
  · exact
      retainedFinalScaledCarrierPrefix_strictlyAvoids_routedClauseChoiceEscape
        formula wellFormed degree isLocal carrier macrocell normalized
        site sourceEq contact choice slot choiceRouteEq
  · exact tailAvoid

/-- In the unresolved carrier--macrocell overlap, routed-clause choice kind
and route representation recover normalization, routed source metadata, and
the local carrier contact automatically.  Only separation from the already
controlled post-escape tail remains as a geometric premise. -/
theorem
    retainedFinalScaledCarrierPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute_of_kind_eq_of_rectangles_not_separated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierTaggedRoute macrocellTaggedRoute : List Cell × Nat}
    (carrier :
      PeriodicOrthocrossing.FinalGaugedFlatCarrierRouteWitness
        formula carrierTaggedRoute)
    (macrocell :
      PeriodicOrthocrossing.FinalGaugedFlatRouteMacrocellWitness
        formula macrocellTaggedRoute)
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (kindEq : choice.kind = RetainedDirectClauseKind.routedClause)
    (choiceRouteEq :
      PeriodicOrthocrossing.translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        macrocellTaggedRoute.1)
    (rectanglesNotSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (PeriodicOrthocrossing.planarSATMacrocellRouteLower
          macrocell.translatedCenter)
        (PeriodicOrthocrossing.planarSATMacrocellRouteUpper
          macrocell.translatedCenter))
    (tailAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline
          (retainedTerminalFanTotalRefinement * 4)
          carrierTaggedRoute.1.dropLast)
        (PeriodicOrthocrossing.translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedDirectSourceFanCompleteTailAt
            choice.kind choice.index slot))) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        carrierTaggedRoute.1.dropLast)
      (choice.completeRoute slot) := by
  rcases macrocell.exists_normalizedSource
      formula wellFormed degree isLocal with
    ⟨normalized⟩
  rcases
      retainedFinalDirectChoice_exists_normalizedRoutedClause_of_kind_eq
        formula wellFormed degree isLocal
        macrocell normalized choice kindEq choiceRouteEq with
    ⟨site, sourceEq⟩
  have normalizedDirect : normalized.source.component.IsDirect := by
    rw [sourceEq]
    trivial
  have contact :=
    carrier.normalizedDirectContact
      formula wellFormed degree isLocal
      macrocell normalized normalizedDirect rectanglesNotSeparated
  exact
    retainedFinalScaledCarrierPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute
      formula wellFormed degree isLocal
      carrier macrocell normalized site sourceEq contact
      choice slot choiceRouteEq tailAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
