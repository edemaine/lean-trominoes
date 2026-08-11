import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSourceCorridorSeparation
import LeanTrominoes.RetainedAngularFanFinalRoutedClausePrefixSeparation

/-!
# Relative routed-clause prefix separation

The ordinary corridor bridge controls every non-routed direct atlas entry.
A routed-clause entry has a longer customized escape, so an overlapping
translated carrier prefix instead uses the transported boundary at the
choice's exact physical origin.  Separated carrier and macrocell components
remain covered by their coarse rectangles.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- Recover the raw component-level atlas choice represented by a successful
final quotient choice for an arbitrary occurrence witness. -/
theorem FinalGaugedRouteOccurrenceWitness.exists_rawChoice_of_finalChoiceSome
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice) :
    ∃ rawChoice : RetainedDirectSourceRouteChoice,
      retainedDirectSourceRouteChoice?
          formula witness.metadata.source literalIndex = some rawChoice ∧
      choice = rawChoice.translateOrigin
        (retainedFinalDirectSourceMetadataTranslation
          formula witness.metadata) := by
  rcases
      retainedFinalDirectSourceRouteChoice_exists_raw
        formula clauseIndex literalIndex choice choiceLookup with
    ⟨metadata, rawChoice, metadataLookup,
      rawLookup, choiceEq⟩
  have witnessMetadataLookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some witness.metadata := by
    have representativeLookup := witness.representativeMetadataLookup
    unfold retainedFinalDirectSourceMetadata?
    exact retainedRepresentativeItem?_eq_some_of_lookups
      (Variable := Variable)
      (Item := DrawingPlanarSATClauseMetadata Variable)
      formula (retainedDrawingPlanarSATClauseMetadata formula)
      clauseIndex witness.finalClause witness.metadata
      witness.finalClauseLookup representativeLookup
  have metadataEq : metadata = witness.metadata :=
    Option.some.inj (metadataLookup.symm.trans witnessMetadataLookup)
  subst metadata
  exact ⟨rawChoice, rawLookup, choiceEq⟩

/-- A represented direct replacement remains in the expanded scaled
macrocell rectangle of an arbitrary final occurrence at shift zero. -/
theorem
    RetainedDirectSourceRouteChoice.completeRoute_point_in_scaledMacrocellRectangle_of_occurrence_routeEq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot)
    (choiceRouteEq :
      translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) =
        finalGaugedRouteOccurrence
          formula clauseIndex literalIndex (0, 0))
    {point : Cell}
    (pointMember : point ∈ choice.completeRoute slot) :
    InClosedGridRectangle
      (coordinateRadiusLower 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          (planarSATMacrocellRouteLower macrocell.translatedCenter)))
      (coordinateRadiusUpper 288
        (Cell.scale
          (retainedTerminalFanTotalRefinement * 4)
          (planarSATMacrocellRouteUpper macrocell.translatedCenter)))
      point := by
  have localLength :=
    retainedDirectSourceLocalRouteAt_length choice.kind choice.index
  rcases List.length_eq_two.mp localLength with
    ⟨localHead, localLast, localRouteEq⟩
  have sourceStartMember :
      choice.sourceSegment.start ∈
        finalGaugedRouteOccurrence
          formula clauseIndex literalIndex (0, 0) := by
    rw [← choiceRouteEq]
    simp [localRouteEq, translatePolyline,
      RetainedDirectSourceRouteChoice.sourceSegment]
  have sourceFinishMember :
      choice.sourceSegment.finish ∈
        finalGaugedRouteOccurrence
          formula clauseIndex literalIndex (0, 0) := by
    rw [← choiceRouteEq]
    simp [localRouteEq, translatePolyline,
      RetainedDirectSourceRouteChoice.sourceSegment]
  have startBound :=
    macrocell.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal
      macrocell.center macrocell.centerEq sourceStartMember
  have finishBound :=
    macrocell.routePoints_in_translatedMacrocell
      formula wellFormed degree isLocal
      macrocell.center macrocell.centerEq sourceFinishMember
  have choiceBound :=
    choice.completeRoute_point_in_sourceSegmentRectangle
      slot pointMember
  rcases choice.sourceSegment.start with ⟨startX, startY⟩
  rcases choice.sourceSegment.finish with ⟨finishX, finishY⟩
  rcases lowerEq : planarSATMacrocellRouteLower
      macrocell.translatedCenter with ⟨lowerX, lowerY⟩
  rcases upperEq : planarSATMacrocellRouteUpper
      macrocell.translatedCenter with ⟨upperX, upperY⟩
  rcases point with ⟨pointX, pointY⟩
  change
    InPlanarSATMacrocell macrocell.translatedCenter
      choice.sourceSegment.start at startBound
  change
    InPlanarSATMacrocell macrocell.translatedCenter
      choice.sourceSegment.finish at finishBound
  simp only [InPlanarSATMacrocell,
    InClosedGridRectangle] at startBound finishBound
  rw [lowerEq, upperEq] at startBound finishBound
  have factorPositive :
      (0 : Int) < retainedTerminalFanTotalRefinement * 4 := by
    native_decide
  simp only [GridSegment.coordinateLower,
    GridSegment.coordinateUpper, coordinateRadiusLower,
    coordinateRadiusUpper, Cell.scale,
    InClosedGridRectangle] at choiceBound ⊢
  norm_num [retainedTerminalFanTotalRefinement_eq]
    at choiceBound factorPositive ⊢
  omega

/-- The routed-clause half-plane escape separator, phrased for a choice
whose kind is propositionally (rather than definitionally) routed-clause. -/
theorem
    retainedScaledOutsidePrefix_strictlyAvoids_choiceEscape_of_kind_eq_routedClause
    (sourceRoute : List Cell)
    (choice : RetainedDirectSourceRouteChoice)
    (port : CornerPort)
    (slot : RetainedTerminalSlot)
    (kindEq : choice.kind = .routedClause)
    (sourceOutside :
      ∀ point ∈ sourceRoute.dropLast,
        port.OutsideCarrierBoundaryAt choice.origin point) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        sourceRoute.dropLast)
      (translatePolyline
        (retainedDirectSourceFanPositioningOffset choice.origin)
        (retainedDirectSourceFanEscapeAt
          choice.kind choice.index slot).route) := by
  rcases choice with ⟨origin, kind, index⟩
  change kind = .routedClause at kindEq
  subst kind
  exact
    retainedScaledOutsidePrefix_strictlyAvoids_positionedRoutedClauseEscape
      sourceRoute origin port index slot sourceOutside

/-- A successful routed-clause final choice has the physical origin of the
routed-clause macrocell occurrence that represents it. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.exists_routedClauseSource_and_choiceOrigin_eq
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (kindEq : choice.kind = .routedClause) :
    ∃ site : ClauseRouteSite,
      macrocell.metadata.source = .routedClause site ∧
      choice.origin =
        Cell.add (routedClauseOrigin formula site)
          macrocell.physicalOffset := by
  let witness := macrocell.toFinalGaugedRouteOccurrenceWitness
  rcases
      witness.exists_rawChoice_of_finalChoiceSome
        formula choice choiceLookup with
    ⟨rawChoice, rawLookup, choiceEq⟩
  have rawKindEq : rawChoice.kind = .routedClause := by
    rw [choiceEq] at kindEq
    exact kindEq
  rcases
      (retainedDirectSourceRouteChoice?_kind_eq_routedClause_iff
        formula witness.metadata.source literalIndex rawChoice rawLookup).mp
        rawKindEq with
    ⟨site, sourceEq⟩
  have rawOriginEq :
      rawChoice.origin = routedClauseOrigin formula site := by
    have routedLookup := rawLookup
    rw [sourceEq] at routedLookup
    simp [retainedDirectSourceRouteChoice?] at routedLookup
    rcases routedLookup with ⟨literalIndexLt, rawChoiceEq⟩
    rw [← rawChoiceEq]
  have translationEq :
      retainedFinalDirectSourceMetadataTranslation
          formula witness.metadata =
        macrocell.physicalOffset := by
    unfold retainedFinalDirectSourceMetadataTranslation
      FinalGaugedRouteMacrocellOccurrenceWitness.physicalOffset
      FinalGaugedRouteOccurrenceWitness.physicalShift
    rw [
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  refine ⟨site, sourceEq, ?_⟩
  rw [choiceEq]
  change
    Cell.add
        (retainedFinalDirectSourceMetadataTranslation
          formula witness.metadata)
        rawChoice.origin =
      Cell.add (routedClauseOrigin formula site)
        macrocell.physicalOffset
  rw [translationEq, rawOriginEq]
  rcases macrocell.physicalOffset with ⟨offsetX, offsetY⟩
  rcases routedClauseOrigin formula site with ⟨originX, originY⟩
  simp [Cell.add]
  constructor <;> ring

/-- At a nonzero relative shift, the scaled failed-choice prefix avoids a
successful routed-clause replacement, including its customized escape. -/
theorem
    retainedFinalTranslatedFallbackSourceScaledPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (kindEq : choice.kind = .routedClause)
    (slot : RetainedTerminalSlot)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        (translatePolyline
          ((finalCoordinatedPlacement formula).translation relativeTranslate)
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex)).dropLast)
      (choice.completeRoute slot) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let directRoute :=
    finalCoordinatedSourceRoutes
      formula directClauseIndex directLiteralIndex
  let fallbackRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let translatedFallbackRoute :=
    translatePolyline
      ((finalCoordinatedPlacement formula).translation relativeTranslate)
      fallbackRoute
  let directOccurrence :=
    finalGaugedRouteOccurrence
      formula directClauseIndex directLiteralIndex (0, 0)
  let fallbackOccurrence :=
    finalGaugedRouteOccurrence
      formula fallbackClauseIndex fallbackLiteralIndex relativeTranslate
  have directOccurrenceEq : directOccurrence = directRoute :=
    (finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
      formula directClauseIndex directLiteralIndex).symm
  have fallbackOccurrenceEq :
      fallbackOccurrence = translatedFallbackRoute := by
    rfl
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        retainedClausesNonempty
        (directClause, directClauseIndex)
        (by simpa [finalCoordinatedSource] using directClauseMember)
        (directLiteral, directLiteralIndex) directLiteralMember
        (0, 0) with
    ⟨directWitness⟩
  rcases
      exists_retainedPhysicalIncidence_of_finalRouteOccurrence
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        retainedClausesNonempty
        (fallbackClause, fallbackClauseIndex)
        (by simpa [finalCoordinatedSource] using fallbackClauseMember)
        (fallbackLiteral, fallbackLiteralIndex) fallbackLiteralMember
        relativeTranslate with
    ⟨fallbackWitness⟩
  have directComponent :
      directWitness.metadata.source.component.IsDirect :=
    directWitness.componentIsDirect_of_finalChoiceSome
      formula choice choiceLookup
  have directNotCarrier :
      ¬∃ link,
        directWitness.metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at directComponent
    simp [DrawingPlanarSATComponent.IsDirect] at directComponent
  rcases
      directWitness.exists_macrocellOccurrenceWitness_of_not_carrier
        directNotCarrier with
    ⟨directMacrocell⟩
  have choiceRouteEq :
      translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt choice.kind choice.index) =
        directOccurrence := by
    rw [directOccurrenceEq]
    exact
      retainedFinalDirectSourceRouteChoice_representsFinalRoute
        formula directClauseIndex directLiteralIndex choice choiceLookup
  rcases
      directMacrocell.exists_routedClauseSource_and_choiceOrigin_eq
        formula choice choiceLookup kindEq with
    ⟨site, directSourceEq, choiceOriginEq⟩
  have directBounded :
      ∀ point ∈ choice.completeRoute slot,
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              (planarSATMacrocellRouteLower
                directMacrocell.translatedCenter)))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * 4)
              (planarSATMacrocellRouteUpper
                directMacrocell.translatedCenter))) point := by
    intro point pointMember
    exact
      _root_.LeanTrominoes.PeriodicOrthocrossing.RetainedDirectSourceRouteChoice.completeRoute_point_in_scaledMacrocellRectangle_of_occurrence_routeEq
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        directMacrocell choice slot choiceRouteEq pointMember
  have corridor :=
    retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone relativeTranslate relativeTranslateNonzero
  have representedSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula directClauseIndex directLiteralIndex choice choiceLookup
  have shiftedTailAvoid :=
    retainedSourceScaledPrefix_strictlyAvoids_directShiftedTail_of_corridorSeparated
      translatedFallbackRoute directRoute choice slot
      (by simpa [directRoute] using representedSegment)
      (by simpa [translatedFallbackRoute, directRoute] using corridor)
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  let directCenter := directRoute.getLastD (0, 0)
  have directCenterMember : directCenter ∈ directRoute := by
    apply getLastD_mem_of_ne_nil
    intro directNil
    rw [directNil] at directLength
    simp at directLength
  have prefixStrict :
      RoutesStrictlyAvoidEachOther
        translatedFallbackRoute.dropLast directRoute := by
    simpa [translatedFallbackRoute, fallbackRoute, directRoute] using
      finalCoordinatedTranslatedSecondSourceRoutePrefix_strictlyAvoids_firstSourceRoute_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        relativeTranslate relativeTranslateNonzero
  have prefixClearance :
      (∀ point ∈ translatedFallbackRoute.dropLast,
          point ≠ directCenter) ∧
      ∀ segment ∈ gridPolylineSegments translatedFallbackRoute.dropLast,
        segment.IsAxisAligned → ¬segment.Contains directCenter := by
    constructor
    · intro point pointMember
      exact prefixStrict.2.2.2 point pointMember
        directCenter directCenterMember
    · intro segment segmentMember _axisAligned contains
      rcases
          GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
            contains with
        interior | endpoint
      · exact
          (prefixStrict.2.2.1 directCenter directCenterMember
            segment segmentMember) interior
      · have endpoints :=
          gridPolylineSegments_endpoints_mem segmentMember
        rcases endpoint with atStart | atFinish
        · exact
            (prefixStrict.2.2.2 segment.start endpoints.1
              directCenter directCenterMember) atStart.symm
        · exact
            (prefixStrict.2.2.2 segment.finish endpoints.2
              directCenter directCenterMember) atFinish.symm
  have localAvoidRaw :=
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_outerLocalRoute
      (factor := 4) (by omega) translatedFallbackRoute directCenter
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 slot
      prefixClearance.1 prefixClearance.2
  have choiceFinishEq : choice.sourceSegment.finish = directCenter := by
    have representedFinish :=
      congrArg GridSegment.finish representedSegment
    simpa [directRoute, directCenter] using representedFinish.symm
  have positionedCenterEq :
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index =
        Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale 4 directCenter) := by
    rw [choice.positionedFanCenter_eq_scale_sourceSegment_finish,
      choiceFinishEq]
    simp [Cell.scale_scale]
  have localAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline
          (retainedTerminalFanTotalRefinement * 4)
          translatedFallbackRoute.dropLast)
        (translatePolyline
          (retainedDirectSourceFanPositioningOffset choice.origin)
          (retainedTerminalFanOuterLocalRouteAt
            (retainedDirectSourceFanCenterAt choice.kind choice.index)
            (retainedDirectSourceFanTerminalAt
              choice.kind choice.index).1 slot)) := by
    rw [choice.positionedLocalRoute_eq, positionedCenterEq]
    rw [scalePolyline_dropLast_eq,
      scalePolyline_dropLast_eq,
      scalePolyline_scalePolyline_nat] at localAvoidRaw
    exact localAvoidRaw
  have tailAvoid :=
    retainedSourcePrefix_strictlyAvoids_directCompleteTail
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        translatedFallbackRoute.dropLast)
      choice slot shiftedTailAvoid localAvoid
  rcases
      fallbackWitness.exists_carrier_or_macrocellOccurrenceWitness with
    fallbackCarrierCase | fallbackMacrocellCase
  · rcases fallbackCarrierCase with ⟨fallbackCarrier⟩
    by_cases rectanglesSeparated :
        ClosedGridRectanglesSeparated
          fallbackCarrier.rectangleLower fallbackCarrier.rectangleUpper
          (planarSATMacrocellRouteLower directMacrocell.translatedCenter)
          (planarSATMacrocellRouteUpper directMacrocell.translatedCenter)
    · apply
        scaledFlatPrefix_strictlyAvoids_directCompleteRoute_of_componentRectanglesSeparated
          (choice := choice) (slot := slot)
          (directBounded := directBounded)
          (rectanglesSeparated := rectanglesSeparated)
      intro point pointMember
      apply fallbackCarrier.routePoints_in_rectangle
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
      change point ∈ fallbackOccurrence
      rw [fallbackOccurrenceEq]
      exact List.mem_of_mem_dropLast pointMember
    · rcases
          fallbackCarrier.exists_routedClauseCarrierOutside_at_physicalOrigin
            formula certificate.graphWellFormed
            certificate.graphDegreeAtMostThree certificate.graphIsLocal
            directMacrocell site directSourceEq rectanglesSeparated with
        ⟨port, carrierOutside⟩
      have escapeAvoid :
          RoutesStrictlyAvoidEachOther
            (scalePolyline
              (retainedTerminalFanTotalRefinement * 4)
              translatedFallbackRoute.dropLast)
            (translatePolyline
              (retainedDirectSourceFanPositioningOffset choice.origin)
              (retainedDirectSourceFanEscapeAt
                choice.kind choice.index slot).route) := by
        exact
          retainedScaledOutsidePrefix_strictlyAvoids_choiceEscape_of_kind_eq_routedClause
            translatedFallbackRoute choice port slot kindEq
            (by
              intro point pointMember
              rw [choiceOriginEq]
              apply carrierOutside point
              change point ∈ fallbackOccurrence
              rw [fallbackOccurrenceEq]
              exact List.mem_of_mem_dropLast pointMember)
      exact
        retainedSourcePrefix_strictlyAvoids_directCompleteRoute_of_pieces
          (scalePolyline
            (retainedTerminalFanTotalRefinement * 4)
            translatedFallbackRoute.dropLast)
          choice slot escapeAvoid tailAvoid
  · rcases fallbackMacrocellCase with ⟨fallbackMacrocell⟩
    have centersDifferent :
        fallbackMacrocell.translatedCenter ≠
          directMacrocell.translatedCenter :=
      fallbackMacrocell.translatedCenter_ne_of_choice_none_of_second_choice_some
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        directMacrocell fallbackChoiceNone choice choiceLookup
    apply
      scaledFlatPrefix_strictlyAvoids_directCompleteRoute_of_componentRectanglesSeparated
        (choice := choice) (slot := slot)
        (directBounded := directBounded)
        (rectanglesSeparated :=
          planarSATMacrocellRouteRectangles_separated centersDifferent)
    intro point pointMember
    apply fallbackMacrocell.routePoints_in_translatedMacrocell
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree certificate.graphIsLocal
      fallbackMacrocell.center fallbackMacrocell.centerEq
    change point ∈ fallbackOccurrence
    rw [fallbackOccurrenceEq]
    exact List.mem_of_mem_dropLast pointMember

/-- Every successful direct replacement avoids the scaled failed-choice
prefix at a nonzero relative shift.  Ordinary choices use the common
corridor; routed-clause choices use the physical-origin escape theorem. -/
theorem
    retainedFinalTranslatedFallbackSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (slot : RetainedTerminalSlot)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline
        (retainedTerminalFanTotalRefinement * 4)
        (translatePolyline
          ((finalCoordinatedPlacement formula).translation relativeTranslate)
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex)).dropLast)
      (choice.completeRoute slot) := by
  by_cases kindEq : choice.kind = .routedClause
  · exact
      retainedFinalTranslatedFallbackSourceScaledPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone kindEq slot relativeTranslate
        relativeTranslateNonzero
  · have corridor :=
      retainedFinalTranslatedFallbackDirect_sourcePrefixCorridorSeparated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        fallbackChoiceNone relativeTranslate relativeTranslateNonzero
    exact
      retainedFinalSourceScaledPrefix_strictlyAvoids_directCompleteRoute_of_corridorSeparated
        formula
        (translatePolyline
          ((finalCoordinatedPlacement formula).translation relativeTranslate)
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))
        directClauseIndex directLiteralIndex choice slot
        choiceLookup kindEq corridor

end PeriodicOrthocrossing
end LeanTrominoes
