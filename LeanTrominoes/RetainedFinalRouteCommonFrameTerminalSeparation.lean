import LeanTrominoes.RetainedFinalRouteCommonFrameBoundaries
import LeanTrominoes.RetainedFinalFlatNormalizedTerminalContactSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceRouteChoice
import LeanTrominoes.RetainedAngularFanSourceSpliceTranslation

/-!
# Terminal rectangles in arbitrary final carrier frames

An arbitrary final occurrence is represented by a retained finite component
plus a physical period shift.  Reindexing a successful direct choice into a
carrier's finite frame translates its origin but leaves its finite atlas kind
and index unchanged.  This file transports the finite equality-lens terminal
dichotomy through that common frame.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit

set_option maxHeartbeats 2400000

/-- A successful final direct choice, decomposed into its raw finite-atlas
choice and the exact origin of that choice in an arbitrary common frame. -/
structure FinalGaugedCommonFrameDirectChoiceData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (reindexShift : Cell) where
  rawChoice : RetainedDirectSourceRouteChoice
  rawLookup :
    retainedDirectSourceRouteChoice?
        formula witness.metadata.source literalIndex = some rawChoice
  choiceEq :
    choice = rawChoice.translateOrigin
      (retainedFinalDirectSourceMetadataTranslation
        formula witness.metadata)
  commonOriginEq :
    Cell.add choice.origin (witness.commonFrameOffset reindexShift) =
      Cell.add rawChoice.origin
        (carrierMacroPeriodTranslation
          formula.incidenceGraph reindexShift)

/-- Every successful final choice has the corresponding raw atlas choice,
and its origin obeys the common-frame translation formula. -/
theorem FinalGaugedRouteOccurrenceWitness.exists_commonFrameDirectChoiceData
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (reindexShift : Cell) :
    Nonempty
      (FinalGaugedCommonFrameDirectChoiceData
        formula witness choice reindexShift) := by
  rcases
      retainedFinalDirectSourceRouteChoice_exists_raw
        formula clauseIndex literalIndex choice choiceLookup with
    ⟨metadata, rawChoice, metadataLookup,
      rawLookup, choiceEq⟩
  have witnessMetadataLookup :
      retainedFinalDirectSourceMetadata? formula clauseIndex =
        some witness.metadata := by
    unfold retainedFinalDirectSourceMetadata?
    rw [witness.finalClauseLookup]
    have representativeLookup := witness.representativeMetadataLookup
    have wrappedDecidableEqEq :
        (@instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (@instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecEq)) =
          (@drawingOrderedWrappedPeriodicPlanarSATVariableInstDecidableEq
            Variable variableDecEq) := by
      funext first second
      exact Subsingleton.elim _ _
    rw [wrappedDecidableEqEq] at representativeLookup
    exact representativeLookup
  have metadataEq : metadata = witness.metadata :=
    Option.some.inj (metadataLookup.symm.trans witnessMetadataLookup)
  subst metadata
  refine ⟨{
    rawChoice := rawChoice
    rawLookup := rawLookup
    choiceEq := choiceEq
    commonOriginEq := ?_
  }⟩
  rw [choiceEq]
  change
    Cell.add
        (Cell.add
          (retainedFinalDirectSourceMetadataTranslation
            formula witness.metadata)
          rawChoice.origin)
        (witness.commonFrameOffset reindexShift) =
      Cell.add rawChoice.origin
        (carrierMacroPeriodTranslation
          formula.incidenceGraph reindexShift)
  unfold retainedFinalDirectSourceMetadataTranslation
    FinalGaugedRouteOccurrenceWitness.commonFrameOffset
    FinalGaugedRouteOccurrenceWitness.physicalShift
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro]
  rcases anchorEq :
      PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause
          formula witness.metadata).literals with
    ⟨anchorX, anchorY⟩
  rcases reindexShift with ⟨reindexX, reindexY⟩
  rcases rawChoice.origin with ⟨originX, originY⟩
  simp [carrierMacroPeriodTranslation,
    Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- The common-frame origin of a routed-clause choice is the translated
routed-clause macrocell origin named by the common source. -/
theorem FinalGaugedCommonFrameDirectChoiceData.commonOrigin_eq_routedClause
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0)}
    {choice : RetainedDirectSourceRouteChoice}
    {reindexShift : Cell}
    (data :
      FinalGaugedCommonFrameDirectChoiceData
        formula witness choice reindexShift)
    (site : ClauseRouteSite)
    (sourceEq :
      witness.commonFrameSource reindexShift =
        .routedClause site) :
    Cell.add choice.origin (witness.commonFrameOffset reindexShift) =
      routedClauseOrigin formula site := by
  cases originalSourceEq : witness.metadata.source with
  | crossover crossing localClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | carrier link localClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | bend routeBend localClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | routedVariable originalSite armIndex arm link localClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | routedClause originalSite =>
      have siteEq :
          clauseRouteSitePeriodTranslate originalSite reindexShift = site := by
        simpa [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
          originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate] using
            sourceEq
      have rawLookup := data.rawLookup
      rw [originalSourceEq] at rawLookup
      simp [retainedDirectSourceRouteChoice?] at rawLookup
      rcases rawLookup with ⟨literalIndexLt, rawChoiceEq⟩
      have rawOriginEq :
          data.rawChoice.origin =
            routedClauseOrigin formula originalSite := by
        rw [← rawChoiceEq]
      rw [data.commonOriginEq, rawOriginEq, ← siteEq,
        routedClauseOrigin_periodTranslate]

/-- The common-frame origin of a routed-variable choice is the translated
routed-variable macrocell origin named by the common source. -/
theorem FinalGaugedCommonFrameDirectChoiceData.commonOrigin_eq_routedVariable
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0)}
    {choice : RetainedDirectSourceRouteChoice}
    {reindexShift : Cell}
    (data :
      FinalGaugedCommonFrameDirectChoiceData
        formula witness choice reindexShift)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (sourceEq :
      witness.commonFrameSource reindexShift =
        .routedVariable
          site armIndex arm link localClauseIndex) :
    Cell.add choice.origin (witness.commonFrameOffset reindexShift) =
      routedVariableOrigin formula site := by
  cases originalSourceEq : witness.metadata.source with
  | crossover crossing originalLocalClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | carrier originalLink originalLocalClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | bend routeBend originalLocalClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | routedClause originalSite =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | routedVariable originalSite originalArmIndex originalArm originalLink
      originalLocalClauseIndex =>
      let siteOf : DrawingPlanarSATClauseSource Variable →
          Option (VariableRouteSite Variable)
        | .routedVariable site _ _ _ _ => some site
        | _ => none
      have translatedSourceEq :
          DrawingPlanarSATClauseSource.routedVariable
              (variableRouteSitePeriodTranslate
                originalSite reindexShift)
              originalArmIndex originalArm
              (planarSATNodeLinkPeriodTranslate
                formula.incidenceGraph originalLink reindexShift)
              originalLocalClauseIndex =
            .routedVariable
              site armIndex arm link localClauseIndex := by
        simpa [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
          originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate] using
            sourceEq
      have siteEq :
          variableRouteSitePeriodTranslate originalSite reindexShift =
            site := by
        have projected := congrArg siteOf translatedSourceEq
        simpa [siteOf] using Option.some.inj projected
      have rawLookup := data.rawLookup
      rw [originalSourceEq] at rawLookup
      simp [retainedDirectSourceRouteChoice?] at rawLookup
      rcases rawLookup with
        ⟨localClauseIndexLt, literalIndexLt, rawChoiceEq⟩
      have rawOriginEq :
          data.rawChoice.origin =
            routedVariableOrigin formula originalSite := by
        rw [← rawChoiceEq]
      rw [data.commonOriginEq, rawOriginEq, ← siteEq,
        routedVariableOrigin_periodTranslate]

/-- The common-frame origin of a crossover choice is the translated
crossover macrocell origin named by the common source. -/
theorem FinalGaugedCommonFrameDirectChoiceData.commonOrigin_eq_crossover
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {clauseIndex literalIndex : Nat}
    {witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0)}
    {choice : RetainedDirectSourceRouteChoice}
    {reindexShift : Cell}
    (data :
      FinalGaugedCommonFrameDirectChoiceData
        formula witness choice reindexShift)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      witness.commonFrameSource reindexShift =
        .crossover crossing localClauseIndex) :
    Cell.add choice.origin (witness.commonFrameOffset reindexShift) =
      crossingMacroOrigin crossing := by
  cases originalSourceEq : witness.metadata.source with
  | carrier link originalLocalClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | bend routeBend originalLocalClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | routedClause site =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | routedVariable site armIndex arm link originalLocalClauseIndex =>
      simp [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate]
        at sourceEq
  | crossover originalCrossing originalLocalClauseIndex =>
      let crossingOf : DrawingPlanarSATClauseSource Variable →
          Option CrossingRecord
        | .crossover crossing _ => some crossing
        | _ => none
      have translatedSourceEq :
          (DrawingPlanarSATClauseSource.crossover
              (originalCrossing.periodTranslate
                formula.incidenceGraph reindexShift)
              originalLocalClauseIndex :
            DrawingPlanarSATClauseSource Variable) =
            .crossover crossing localClauseIndex := by
        simpa [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
          originalSourceEq, DrawingPlanarSATClauseSource.periodTranslate] using
            sourceEq
      have crossingEq :
          originalCrossing.periodTranslate
              formula.incidenceGraph reindexShift = crossing := by
        have projected := congrArg crossingOf translatedSourceEq
        simpa [crossingOf] using Option.some.inj projected
      have rawLookup := data.rawLookup
      rw [originalSourceEq] at rawLookup
      simp [retainedDirectSourceRouteChoice?] at rawLookup
      rcases rawLookup with
        ⟨localClauseIndexLt, literalIndexLt, rawChoiceEq⟩
      have rawOriginEq :
          data.rawChoice.origin =
            crossingMacroOrigin originalCrossing := by
        rw [← rawChoiceEq]
      rw [data.commonOriginEq, rawOriginEq, ← crossingEq,
        crossingMacroOrigin_periodTranslate]

/-- The selected final atlas route, moved into any common frame, is still
the positioned local atlas route with its origin moved into that frame. -/
theorem RetainedDirectSourceRouteChoice.commonFrameRoute_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (reindexShift : Cell) :
    translatePolyline
        (Cell.add choice.origin
          (macrocell.commonFrameOffset reindexShift))
        (retainedDirectSourceLocalRouteAt choice.kind choice.index) =
      macrocell.commonFrameRoute reindexShift := by
  unfold FinalGaugedRouteOccurrenceWitness.commonFrameRoute
  rw [←
    finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
      formula clauseIndex literalIndex]
  have represents :
      translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt choice.kind choice.index) =
        finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex := by
    exact
      retainedFinalDirectSourceRouteChoice_representsFinalRoute
        formula clauseIndex literalIndex choice choiceLookup
  rw [← represents]
  exact
    (translatePolyline_add choice.origin
      (macrocell.commonFrameOffset reindexShift)
      (retainedDirectSourceLocalRouteAt
        choice.kind choice.index)).symm

/-- Translation commutes with the penultimate-point lookup on a genuine
polyline. -/
theorem polylineLastEntrance_translatePolyline
    (offset : Cell) (route : List Cell)
    (routeLength : 2 ≤ route.length) :
    polylineLastEntrance (translatePolyline offset route) =
      Cell.add offset (polylineLastEntrance route) := by
  have reverseTailExists :=
    exists_reverse_tail_head?_of_two_le_length route routeLength
  have entranceSpec :=
    polylineLastEntrance_spec reverseTailExists
  have translatedSpec :
      (translatePolyline offset route).reverse.tail.head? =
        some (Cell.add offset (polylineLastEntrance route)) := by
    rw [translatePolyline, ← List.map_reverse]
    rw [show
      (List.map (Cell.add offset) route.reverse).tail =
        List.map (Cell.add offset) route.reverse.tail by
          cases route.reverse <;> rfl]
    rw [List.head?_map, entranceSpec]
    rfl
  exact polylineLastEntrance_eq translatedSpec

/-- Translation commutes with the total final-segment construction on a
genuine polyline. -/
theorem finalGridSegment_translatePolyline
    (offset : Cell) (route : List Cell)
    (routeLength : 2 ≤ route.length) :
    (GridSegment.mk
      (polylineLastEntrance (translatePolyline offset route))
      ((translatePolyline offset route).getLastD (0, 0))) =
      (GridSegment.mk
        (polylineLastEntrance route)
        (route.getLastD (0, 0))).translate offset := by
  have routeNonempty : route ≠ [] := by
    intro routeNil
    rw [routeNil] at routeLength
    simp at routeLength
  rw [polylineLastEntrance_translatePolyline offset route routeLength,
    translatePolyline_getLastD offset route routeNonempty]
  rfl

/-- A final-segment dichotomy proved after translating two routes by the
same offset reflects back to the original routes. -/
theorem finalGridSegmentDichotomy_of_commonFrame
    (firstRoute secondRoute : List Cell)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstOffset secondOffset : Cell)
    (offsetEq : firstOffset = secondOffset)
    (commonDichotomy :
      let firstFinal : GridSegment :=
        GridSegment.mk
          (polylineLastEntrance
            (translatePolyline firstOffset firstRoute))
          ((translatePolyline firstOffset firstRoute).getLastD (0, 0))
      let secondFinal : GridSegment :=
        GridSegment.mk
          (polylineLastEntrance
            (translatePolyline secondOffset secondRoute))
          ((translatePolyline secondOffset secondRoute).getLastD (0, 0))
      ClosedGridRectanglesSeparated
          firstFinal.coordinateLower firstFinal.coordinateUpper
          secondFinal.coordinateLower secondFinal.coordinateUpper ∨
        firstFinal.finish = secondFinal.finish) :
    let firstFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance firstRoute)
        (firstRoute.getLastD (0, 0))
    let secondFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance secondRoute)
        (secondRoute.getLastD (0, 0))
    ClosedGridRectanglesSeparated
        firstFinal.coordinateLower firstFinal.coordinateUpper
        secondFinal.coordinateLower secondFinal.coordinateUpper ∨
      firstFinal.finish = secondFinal.finish := by
  subst secondOffset
  rw [finalGridSegment_translatePolyline
      firstOffset firstRoute firstLength,
    finalGridSegment_translatePolyline
      firstOffset secondRoute secondLength] at commonDichotomy
  rcases commonDichotomy with separated | finishEq
  · left
    rw [GridSegment.coordinateLower_translate,
      GridSegment.coordinateUpper_translate,
      GridSegment.coordinateLower_translate,
      GridSegment.coordinateUpper_translate] at separated
    exact
      (ClosedGridRectanglesSeparated.add_iff
        _ _ _ _ firstOffset).mp separated
  · right
    exact Cell.add_left_injective firstOffset finishEq

/-- The final segment of a common-frame selected direct route is the local
atlas segment translated to the choice's common-frame origin. -/
theorem RetainedDirectSourceRouteChoice.commonFrameFinalSegment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (reindexShift : Cell) :
    (GridSegment.mk
      (polylineLastEntrance
        (macrocell.commonFrameRoute reindexShift))
      ((macrocell.commonFrameRoute reindexShift).getLastD (0, 0))) =
      (GridSegment.mk
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).headD (0, 0))
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0))).translate
          (Cell.add choice.origin
            (macrocell.commonFrameOffset reindexShift)) := by
  have localLength :=
    retainedDirectSourceLocalRouteAt_length choice.kind choice.index
  rcases List.length_eq_two.mp localLength with
    ⟨localHead, localLast, localRouteEq⟩
  rw [←
    RetainedDirectSourceRouteChoice.commonFrameRoute_eq
      formula macrocell choice choiceLookup reindexShift]
  simp [localRouteEq, translatePolyline,
    polylineLastEntrance, polylineFirstExit,
    GridSegment.translate]

/-- Obliqueness of a positioned direct choice reflects to its untranslated
finite atlas segment. -/
theorem RetainedDirectSourceRouteChoice.localSegment_not_axisAligned
    (choice : RetainedDirectSourceRouteChoice)
    (directOblique : ¬choice.sourceSegment.IsAxisAligned) :
    ¬(GridSegment.mk
      ((retainedDirectSourceLocalRouteAt
          choice.kind choice.index).headD (0, 0))
      ((retainedDirectSourceLocalRouteAt
          choice.kind choice.index).getLastD (0, 0))).IsAxisAligned := by
  intro localAligned
  apply directOblique
  exact
    (GridSegment.isAxisAligned_translate
      (GridSegment.mk
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).headD (0, 0))
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0)))
      choice.origin).mpr localAligned

/-- A common-frame selected carrier route, exposed as an exact route of its
finite equality lens with bounded presentation indices. -/
structure FinalGaugedCommonFrameCarrierLensData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell)
    (link : EqualityLink CarrierNode) where
  localClauseIndex : Nat
  selection :
    FinalGaugedFlatNormalizedRouteSelection
      formula (carrier.commonFrameRoute reindexShift, clauseIndex)
        (.carrier link localClauseIndex)
  localClauseIndexLt : localClauseIndex < 2
  literalIndexLt : selection.literalIndex < 2
  routeEq :
    carrier.commonFrameRoute reindexShift =
      (EqualityLink.lensDrawing
        (CarrierNode.position formula.incidenceGraph) link).routes
          localClauseIndex selection.literalIndex

/-- Every raw retained common-frame carrier presentation supplies its
intrinsic equality-lens selection. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.exists_commonFrameCarrierLensData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (reindexShift : Cell)
    (rawMember :
      carrierLinkPeriodTranslate formula.incidenceGraph
          carrier.link reindexShift ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph) :
    Nonempty
      (FinalGaugedCommonFrameCarrierLensData
        formula carrier reindexShift
          (carrierLinkPeriodTranslate
            formula.incidenceGraph carrier.link reindexShift)) := by
  let link :=
    carrierLinkPeriodTranslate
      formula.incidenceGraph carrier.link reindexShift
  rcases
      carrier.exists_commonFrameRouteSelection
        formula wellFormed degree isLocal reindexShift rawMember with
    ⟨localClauseIndex, ⟨selection⟩⟩
  have localClauseIndexLt : localClauseIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx selection.clauseMember
    change
      localClauseIndex <
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula.length at indexLt
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal rawMember] at indexLt
    simpa [drawingPlanarSATCarrierFormulaAt,
      equalityInstance] using indexLt
  have literalIndexLt : selection.literalIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx selection.literalMember
    have clauseMember :=
      List.fst_mem_of_mem_zipIdx selection.clauseMember
    change
      selection.clause ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).formula at clauseMember
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal rawMember] at clauseMember
    have clauseLength : selection.clause.literals.length = 2 := by
      simp [drawingPlanarSATCarrierFormulaAt,
        equalityInstance] at clauseMember
      rcases clauseMember with clauseEq | clauseEq
      · rw [clauseEq]
        simp [EmbeddedClause.rename, EmbeddedClause.map]
      · rw [clauseEq]
        simp [EmbeddedClause.rename, EmbeddedClause.map]
    simpa [clauseLength] using indexLt
  refine ⟨{
    localClauseIndex := localClauseIndex
    selection := selection
    localClauseIndexLt := localClauseIndexLt
    literalIndexLt := literalIndexLt
    routeEq := ?_
  }⟩
  simpa [link, DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex,
    drawingPlanarSATCarrierLensIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename] using selection.routeEq

/-- The finite first-end equality-lens dichotomy, stated for a selected
carrier route and a successful final direct choice in one common frame. -/
private theorem commonFrameFinalSegments_firstEndpoint_dichotomy
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift carrierReindex macrocellReindex : Cell}
    {carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift}
    (link : EqualityLink CarrierNode)
    (rawMember :
      link ∈ retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph)
    (carrierData :
      FinalGaugedCommonFrameCarrierLensData
        formula carrier carrierReindex link)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula macrocellClauseIndex macrocellLiteralIndex = some choice)
    (originEq :
      Cell.add choice.origin
          (macrocell.commonFrameOffset macrocellReindex) =
        EqualityLink.firstCarrierMacroOrigin
          (CarrierNode.position formula.incidenceGraph) link)
    (directOblique : ¬choice.sourceSegment.IsAxisAligned) :
    let carrierFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance (carrier.commonFrameRoute carrierReindex))
        ((carrier.commonFrameRoute carrierReindex).getLastD (0, 0))
    let macrocellFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance (macrocell.commonFrameRoute macrocellReindex))
        ((macrocell.commonFrameRoute macrocellReindex).getLastD (0, 0))
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
      carrierFinal.finish = macrocellFinal.finish := by
  have geometry :=
    retainedDrawingCompleteCarrierLinkRaw_lensGeometry
      wellFormed degree isLocal rawMember
  have dichotomy :=
    PeriodicEightOccurrenceSplit.EqualityLink.lensDrawing_first_finalSegmentRectanglesSeparated_or_finish_eq_nat
      geometry carrierData.localClauseIndex
      carrierData.selection.literalIndex
      carrierData.localClauseIndexLt carrierData.literalIndexLt
      choice.kind choice.index
      (RetainedDirectSourceRouteChoice.localSegment_not_axisAligned
        choice directOblique)
  have positionedDirectEq :
      (GridSegment.mk
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).headD (0, 0))
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0))).translate
          (EqualityLink.firstCarrierMacroOrigin
            (CarrierNode.position formula.incidenceGraph) link) =
        GridSegment.mk
          (polylineLastEntrance (macrocell.commonFrameRoute macrocellReindex))
          ((macrocell.commonFrameRoute macrocellReindex).getLastD (0, 0)) := by
    rw [← originEq]
    exact
      (RetainedDirectSourceRouteChoice.commonFrameFinalSegment_eq
        formula macrocell choice choiceLookup macrocellReindex).symm
  rw [← carrierData.routeEq, positionedDirectEq] at dichotomy
  exact dichotomy

/-- The second-end counterpart of
`commonFrameFinalSegments_firstEndpoint_dichotomy`. -/
private theorem commonFrameFinalSegments_secondEndpoint_dichotomy
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift carrierReindex macrocellReindex : Cell}
    {carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift}
    (link : EqualityLink CarrierNode)
    (rawMember :
      link ∈ retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph)
    (carrierData :
      FinalGaugedCommonFrameCarrierLensData
        formula carrier carrierReindex link)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula macrocellClauseIndex macrocellLiteralIndex = some choice)
    (originEq :
      Cell.add choice.origin
          (macrocell.commonFrameOffset macrocellReindex) =
        EqualityLink.secondCarrierMacroOrigin
          (CarrierNode.position formula.incidenceGraph) link)
    (directOblique : ¬choice.sourceSegment.IsAxisAligned) :
    let carrierFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance (carrier.commonFrameRoute carrierReindex))
        ((carrier.commonFrameRoute carrierReindex).getLastD (0, 0))
    let macrocellFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance (macrocell.commonFrameRoute macrocellReindex))
        ((macrocell.commonFrameRoute macrocellReindex).getLastD (0, 0))
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
      carrierFinal.finish = macrocellFinal.finish := by
  have geometry :=
    retainedDrawingCompleteCarrierLinkRaw_lensGeometry
      wellFormed degree isLocal rawMember
  have dichotomy :=
    PeriodicEightOccurrenceSplit.EqualityLink.lensDrawing_second_finalSegmentRectanglesSeparated_or_finish_eq_nat
      geometry carrierData.localClauseIndex
      carrierData.selection.literalIndex
      carrierData.localClauseIndexLt carrierData.literalIndexLt
      choice.kind choice.index
      (RetainedDirectSourceRouteChoice.localSegment_not_axisAligned
        choice directOblique)
  have positionedDirectEq :
      (GridSegment.mk
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).headD (0, 0))
        ((retainedDirectSourceLocalRouteAt
            choice.kind choice.index).getLastD (0, 0))).translate
          (EqualityLink.secondCarrierMacroOrigin
            (CarrierNode.position formula.incidenceGraph) link) =
        GridSegment.mk
          (polylineLastEntrance (macrocell.commonFrameRoute macrocellReindex))
          ((macrocell.commonFrameRoute macrocellReindex).getLastD (0, 0)) := by
    rw [← originEq]
    exact
      (RetainedDirectSourceRouteChoice.commonFrameFinalSegment_eq
        formula macrocell choice choiceLookup macrocellReindex).symm
  rw [← carrierData.routeEq, positionedDirectEq] at dichotomy
  exact dichotomy

/-- At every overlapping contact between an arbitrary selected carrier
occurrence and an oblique successful direct route at shift zero, their final
segment rectangles are separated unless their final endpoints agree. -/
theorem
    FinalGaugedCarrierRouteOccurrenceWitness.finalSegmentRectanglesSeparated_or_finish_eq_of_directChoice_of_notSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift : Cell}
    (carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift)
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex (0, 0))
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula macrocellClauseIndex macrocellLiteralIndex = some choice)
    (direct : macrocell.metadata.source.component.IsDirect)
    (directOblique : ¬choice.sourceSegment.IsAxisAligned)
    (carrierLength :
      2 ≤ (finalGaugedRouteOccurrence formula
        carrierClauseIndex carrierLiteralIndex carrierShift).length)
    (macrocellLength :
      2 ≤ (finalGaugedRouteOccurrence formula
        macrocellClauseIndex macrocellLiteralIndex (0, 0)).length)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        carrier.rectangleLower carrier.rectangleUpper
        (planarSATMacrocellRouteLower macrocell.translatedCenter)
        (planarSATMacrocellRouteUpper macrocell.translatedCenter)) :
    let carrierRoute :=
      finalGaugedRouteOccurrence formula
        carrierClauseIndex carrierLiteralIndex carrierShift
    let macrocellRoute :=
      finalGaugedRouteOccurrence formula
        macrocellClauseIndex macrocellLiteralIndex (0, 0)
    let carrierFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance carrierRoute)
        (carrierRoute.getLastD (0, 0))
    let macrocellFinal : GridSegment :=
      GridSegment.mk
        (polylineLastEntrance macrocellRoute)
        (macrocellRoute.getLastD (0, 0))
    ClosedGridRectanglesSeparated
        carrierFinal.coordinateLower carrierFinal.coordinateUpper
        macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
      carrierFinal.finish = macrocellFinal.finish := by
  have rawCarrierMember :
      carrier.link ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph :=
    (mem_retainedDrawingCompleteCarrierLinks_iff
      formula.incidenceGraph carrier.link).mp carrier.link_mem |>.1
  rcases
      carrier.crossover_or_carrierFrameTerminalContact
        formula wellFormed degree isLocal macrocell direct notSeparated with
    crossover | terminal
  · obtain ⟨crossing, localClauseIndex, sourceEq⟩ := crossover
    let carrierReindex :=
      carrier.normalizedCrossoverShift macrocell crossing
    let macrocellReindex :=
      Cell.neg (crossingPeriodShift formula.incidenceGraph crossing)
    let normalizedLink :=
      carrier.normalizedCrossoverLink macrocell crossing
    let normalizedCrossing :=
      crossing.periodNormalize formula.incidenceGraph
    have centerEq : macrocell.center = crossing.point := by
      have advertised := macrocell.centerEq
      rw [sourceEq] at advertised
      simpa [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter] using
          Option.some.inj advertised.symm
    have rawMember :
        normalizedLink ∈
          retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph := by
      exact carrier.normalizedCrossoverLink_mem_raw
        wellFormed degree isLocal macrocell crossing centerEq notSeparated
    rcases
        carrier.exists_commonFrameCarrierLensData
          formula wellFormed degree isLocal carrierReindex rawMember with
      ⟨carrierData⟩
    rcases
        macrocell.exists_commonFrameDirectChoiceData
          formula choice choiceLookup macrocellReindex with
      ⟨directData⟩
    have translatedSourceEq :
        macrocell.commonFrameSource macrocellReindex =
          .crossover normalizedCrossing localClauseIndex := by
      unfold FinalGaugedRouteOccurrenceWitness.commonFrameSource
      simp [sourceEq, macrocellReindex, normalizedCrossing,
        DrawingPlanarSATClauseSource.periodTranslate,
        CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize]
    have directOrigin :=
      directData.commonOrigin_eq_crossover
        normalizedCrossing localClauseIndex translatedSourceEq
    have incident :
        CarrierLinkIncidentToCrossover normalizedLink normalizedCrossing := by
      exact carrier.normalizedCrossoverContact
        formula wellFormed degree isLocal macrocell crossing
        localClauseIndex sourceEq notSeparated
    have offsetEq :
        carrier.commonFrameOffset carrierReindex =
          macrocell.commonFrameOffset macrocellReindex := by
      exact carrier.commonFrameOffset_normalizedCrossover_eq
        macrocell crossing
    rcases incident with ⟨side, firstEqual | secondEqual⟩
    · have carrierOrigin :=
        retainedDrawingCompleteCarrierLinkRaw_firstCarrierMacroOrigin_eq_boundary
          wellFormed degree isLocal rawMember firstEqual
      have commonDichotomy :=
        commonFrameFinalSegments_firstEndpoint_dichotomy
          formula wellFormed degree isLocal normalizedLink rawMember
          carrierData macrocell choice choiceLookup
          (directOrigin.trans carrierOrigin.symm) directOblique
      exact
        finalGridSegmentDichotomy_of_commonFrame
          (finalGaugedRouteOccurrence formula
            carrierClauseIndex carrierLiteralIndex carrierShift)
          (finalGaugedRouteOccurrence formula
            macrocellClauseIndex macrocellLiteralIndex (0, 0))
          carrierLength macrocellLength
          (carrier.commonFrameOffset carrierReindex)
          (macrocell.commonFrameOffset macrocellReindex)
          offsetEq commonDichotomy
    · have carrierOrigin :=
        retainedDrawingCompleteCarrierLinkRaw_secondCarrierMacroOrigin_eq_boundary
          wellFormed degree isLocal rawMember secondEqual
      have commonDichotomy :=
        commonFrameFinalSegments_secondEndpoint_dichotomy
          formula wellFormed degree isLocal normalizedLink rawMember
          carrierData macrocell choice choiceLookup
          (directOrigin.trans carrierOrigin.symm) directOblique
      exact
        finalGridSegmentDichotomy_of_commonFrame
          (finalGaugedRouteOccurrence formula
            carrierClauseIndex carrierLiteralIndex carrierShift)
          (finalGaugedRouteOccurrence formula
            macrocellClauseIndex macrocellLiteralIndex (0, 0))
          carrierLength macrocellLength
          (carrier.commonFrameOffset carrierReindex)
          (macrocell.commonFrameOffset macrocellReindex)
          offsetEq commonDichotomy
  · let relativeShift := macrocell.relativeShiftFrom carrier
    have rawZero :
        carrierLinkPeriodTranslate formula.incidenceGraph
            carrier.link (0, 0) ∈
          retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph := by
      simpa using rawCarrierMember
    rcases
        carrier.exists_commonFrameCarrierLensData
          formula wellFormed degree isLocal (0, 0) rawZero with
      ⟨carrierData⟩
    have carrierData' :
        FinalGaugedCommonFrameCarrierLensData
          formula carrier (0, 0) carrier.link := by
      simpa using carrierData
    rcases
        macrocell.exists_commonFrameDirectChoiceData
          formula choice choiceLookup relativeShift with
      ⟨directData⟩
    have offsetEq :
        carrier.commonFrameOffset (0, 0) =
          macrocell.commonFrameOffset relativeShift := by
      exact carrier.commonFrameOffset_zero_eq_relative macrocell
    have finish
        (commonDichotomy :
          let carrierFinal : GridSegment :=
            GridSegment.mk
              (polylineLastEntrance (carrier.commonFrameRoute (0, 0)))
              ((carrier.commonFrameRoute (0, 0)).getLastD (0, 0))
          let macrocellFinal : GridSegment :=
            GridSegment.mk
              (polylineLastEntrance
                (macrocell.commonFrameRoute relativeShift))
              ((macrocell.commonFrameRoute relativeShift).getLastD (0, 0))
          ClosedGridRectanglesSeparated
              carrierFinal.coordinateLower carrierFinal.coordinateUpper
              macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
            carrierFinal.finish = macrocellFinal.finish) :
        let carrierRoute :=
          finalGaugedRouteOccurrence formula
            carrierClauseIndex carrierLiteralIndex carrierShift
        let macrocellRoute :=
          finalGaugedRouteOccurrence formula
            macrocellClauseIndex macrocellLiteralIndex (0, 0)
        let carrierFinal : GridSegment :=
          GridSegment.mk
            (polylineLastEntrance carrierRoute)
            (carrierRoute.getLastD (0, 0))
        let macrocellFinal : GridSegment :=
          GridSegment.mk
            (polylineLastEntrance macrocellRoute)
            (macrocellRoute.getLastD (0, 0))
        ClosedGridRectanglesSeparated
            carrierFinal.coordinateLower carrierFinal.coordinateUpper
            macrocellFinal.coordinateLower macrocellFinal.coordinateUpper ∨
          carrierFinal.finish = macrocellFinal.finish := by
      exact
        finalGridSegmentDichotomy_of_commonFrame
          (finalGaugedRouteOccurrence formula
            carrierClauseIndex carrierLiteralIndex carrierShift)
          (finalGaugedRouteOccurrence formula
            macrocellClauseIndex macrocellLiteralIndex (0, 0))
          carrierLength macrocellLength
          (carrier.commonFrameOffset (0, 0))
          (macrocell.commonFrameOffset relativeShift)
          offsetEq commonDichotomy
    rcases terminal with routedClauseContact | routedVariableContact
    · obtain ⟨site, occurrence, data⟩ := routedClauseContact
      have sourceEq := data.1
      have occurrenceMember := data.2.2.1
      have incident := data.2.2.2
      have translatedSourceEq :
          macrocell.commonFrameSource relativeShift =
            .routedClause site := by
        exact sourceEq
      have directOrigin :=
        directData.commonOrigin_eq_routedClause site translatedSourceEq
      rcases incident with firstEqual | secondEqual
      · have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_first_sourceTerminalInterface
            wellFormed degree isLocal rawCarrierMember site
            occurrenceMember firstEqual).2
        exact finish
          (commonFrameFinalSegments_firstEndpoint_dichotomy
            formula wellFormed degree isLocal carrier.link rawCarrierMember
            carrierData' macrocell choice choiceLookup
            (directOrigin.trans carrierOrigin.symm) directOblique)
      · have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_second_sourceTerminalInterface
            wellFormed degree isLocal rawCarrierMember site
            occurrenceMember secondEqual).2
        exact finish
          (commonFrameFinalSegments_secondEndpoint_dichotomy
            formula wellFormed degree isLocal carrier.link rawCarrierMember
            carrierData' macrocell choice choiceLookup
            (directOrigin.trans carrierOrigin.symm) directOblique)
    · obtain
        ⟨site, armIndex, arm, link, localClauseIndex,
          occurrence, data⟩ := routedVariableContact
      have sourceEq := data.1
      have occurrenceMember := data.2.2.1
      have incident := data.2.2.2
      have translatedSourceEq :
          macrocell.commonFrameSource relativeShift =
            .routedVariable site armIndex arm link localClauseIndex := by
        exact sourceEq
      have directOrigin :=
        directData.commonOrigin_eq_routedVariable
          site armIndex arm link localClauseIndex translatedSourceEq
      rcases incident with firstEqual | secondEqual
      · have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_first_targetTerminalInterface
            wellFormed degree isLocal rawCarrierMember site
            occurrenceMember firstEqual).2
        exact finish
          (commonFrameFinalSegments_firstEndpoint_dichotomy
            formula wellFormed degree isLocal carrier.link rawCarrierMember
            carrierData' macrocell choice choiceLookup
            (directOrigin.trans carrierOrigin.symm) directOblique)
      · have carrierOrigin :=
          (retainedDrawingCompleteCarrierLinkRaw_second_targetTerminalInterface
            wellFormed degree isLocal rawCarrierMember site
            occurrenceMember secondEqual).2
        exact finish
          (commonFrameFinalSegments_secondEndpoint_dichotomy
            formula wellFormed degree isLocal carrier.link rawCarrierMember
            carrierData' macrocell choice choiceLookup
            (directOrigin.trans carrierOrigin.symm) directOblique)

end PeriodicOrthocrossing
end LeanTrominoes
