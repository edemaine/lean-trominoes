import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSameCenterBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceOtherSpokeSeparation
import LeanTrominoes.RetainedAngularFanDirectSourceCrossClauseSameTargetSeparation

/-!
# Periodic same-center mixed spoke separation

At a common physical target, the selected direct and translated fallback
Figure 7 suffixes are positioned copies of the same finite spoke family.
Strict angular order makes their slots distinct, so the finite local spoke
certificates settle the prefix--suffix and suffix--suffix interactions.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A positioned direct choice's Figure 7 spoke is the standard centered
spoke at its positioned fan center. -/
theorem retainedDirectSourceRouteChoice_figure7Spoke_eq_spokeRouteAt
    (choice : RetainedDirectSourceRouteChoice)
    (slot : RetainedTerminalSlot) :
    choice.figure7Spoke slot =
      retainedTerminalFanFigure7SpokeRouteAt
        (retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index)
        slot := by
  rw [choice.figure7Spoke_eq_translate]
  unfold retainedTerminalFanFigure7SpokeRouteAt
    retainedDirectSourcePositionedFanCenterAt
  rw [translatePolyline_add]
  apply congrArg₂ translatePolyline
  · rcases retainedDirectSourceFanPositioningOffset choice.origin with
      ⟨offsetX, offsetY⟩
    rcases retainedDirectSourceFanCenterAt choice.kind choice.index with
      ⟨centerX, centerY⟩
    simp [Cell.add, Cell.sub, Cell.scale]
    constructor <;> ring
  · rfl

/-- A translated fallback canonical center is the positioned direct fan
center when the two retained occurrences share that physical target. -/
theorem
    retainedFinalDirectPositionedFanCenter_eq_add_translatedFallbackCanonicalFanCenter_of_sameCenter
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
    {directClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (relativeTranslate : Cell)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    retainedDirectSourcePositionedFanCenterAt
        choice.origin choice.kind choice.index =
      Cell.add
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (Cell.scale retainedTerminalFanTotalRefinement
          (Cell.scale retainedAngularFanSourceClearanceFactor
            (PositionedPeriodicCNF.canonicalLiteralPosition
              (finalCoordinatedPlacement formula)
              fallbackClause fallbackLiteral))) := by
  have directFinish :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember
      directLiteralMember choiceLookup
  rw [choice.positionedFanCenter_eq_scale_sourceSegment_finish,
    directFinish, centersEqual,
    retainedFinalPhysicalTranslation_eq_refinedSourceTranslation]
  rcases (finalCoordinatedPlacement formula).translation
      relativeTranslate with ⟨translateX, translateY⟩
  rcases PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula)
      fallbackClause fallbackLiteral with ⟨centerX, centerY⟩
  simp [retainedAngularFanSourceClearanceFactor,
    Cell.add, Cell.scale]
  constructor <;> ring

/-- The two existing normal forms for a centered refined Figure 7 spoke
coincide. -/
theorem retainedTerminalFanFigure7SpokeAt_eq_spokeRouteAt
    (center : Cell)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanFigure7SpokeAt center slot =
      retainedTerminalFanFigure7SpokeRouteAt center slot := by
  unfold retainedTerminalFanFigure7SpokeAt
    retainedTerminalFanFigure7SpokeRouteAt
  rw [translatePolyline_add]
  apply congrArg₂ translatePolyline
  · rcases center with ⟨centerX, centerY⟩
    simp [Cell.add, Cell.sub, Cell.scale]
    constructor <;> ring
  · rfl

/-- Translating a centered spoke translates its center. -/
theorem translatePolyline_retainedTerminalFanFigure7SpokeRouteAt
    (offset center : Cell)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanFigure7SpokeRouteAt center slot) =
      retainedTerminalFanFigure7SpokeRouteAt
        (Cell.add offset center) slot := by
  unfold retainedTerminalFanFigure7SpokeRouteAt translatePolyline
  simp only [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases offset with ⟨offsetX, offsetY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- Strict angular compatibility in particular assigns different occurrence
slots. -/
theorem directFallbackStrictAngularOrderCompatible_slots_ne
    (directDirection fallbackDirection : RetainedTerminalDirection)
    (directSlot fallbackSlot : RetainedTerminalSlot)
    (angularOrder :
      DirectFallbackStrictAngularOrderCompatible
        directDirection fallbackDirection directSlot fallbackSlot) :
    directSlot ≠ fallbackSlot := by
  intro slotsEqual
  subst fallbackSlot
  rcases angularOrder with ⟨slotsLt, _⟩ | ⟨slotsLt, _⟩ <;>
    exact (Nat.lt_irrefl _ slotsLt)

/-- Different positioned spokes of a single direct choice are strictly
separated. -/
theorem retainedDirectSourceRouteChoice_figure7Spokes_strictlyAvoid
    (choice : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (slotsDifferent : firstSlot ≠ secondSlot) :
    RoutesStrictlyAvoidEachOther
      (choice.figure7Spoke firstSlot)
      (choice.figure7Spoke secondSlot) := by
  rw [retainedDirectSourceRouteChoice_figure7Spoke_eq_spokeRouteAt,
    retainedDirectSourceRouteChoice_figure7Spoke_eq_spokeRouteAt,
    ← retainedTerminalFanFigure7SpokeAt_eq_spokeRouteAt,
    ← retainedTerminalFanFigure7SpokeAt_eq_spokeRouteAt]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne slotsDifferent) with
      slotsLt | slotsLt
  · exact
      retainedTerminalFanFigure7SpokesAt_strictlyAvoid
        (retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index)
        firstSlot secondSlot slotsLt
  · exact
      (retainedTerminalFanFigure7SpokesAt_strictlyAvoid
        (retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index)
        secondSlot firstSlot slotsLt).symm

/-- At a common physical center, the translated fallback suffix is exactly
the corresponding positioned direct-choice spoke. -/
theorem
    retainedFinalTranslatedFallbackOccurrenceSuffix_eq_directFigure7Spoke_of_sameCenter
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
    (relativeTranslate : Cell)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let fallbackSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
    let physicalTranslate :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate
    translatePolyline physicalTranslate
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
            fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)) =
      choice.figure7Spoke fallbackSlot := by
  dsimp only
  let rawRoute :=
    finalCoordinatedSourceRoutes
      formula fallbackClauseIndex fallbackLiteralIndex
  let sourceTranslate :=
    (finalCoordinatedPlacement formula).translation relativeTranslate
  let translatedRawRoute := translatePolyline sourceTranslate rawRoute
  let fallbackCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale retainedAngularFanSourceClearanceFactor
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral))
  let translatedCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline retainedAngularFanSourceClearanceFactor
        translatedRawRoute).getLastD (0, 0))
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  have fallbackEndpoint :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember).2
  have rawRouteNonempty : rawRoute ≠ [] := by
    intro routeEmpty
    change rawRoute.getLast? = _ at fallbackEndpoint
    rw [routeEmpty] at fallbackEndpoint
    simp at fallbackEndpoint
  have translatedCenterEq :
      translatedCenter = Cell.add physicalTranslate fallbackCenter := by
    dsimp [translatedCenter, translatedRawRoute]
    rw [scalePolyline_getLastD,
      translatePolyline_getLastD sourceTranslate rawRoute rawRouteNonempty]
    have rawLastD :
        rawRoute.getLastD (0, 0) =
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral := by
      rw [List.getLastD_eq_getLast?, show rawRoute.getLast? = _ by
        simpa [rawRoute] using fallbackEndpoint]
      rfl
    rw [rawLastD]
    have physicalTranslateEq :
        physicalTranslate =
          Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale retainedAngularFanSourceClearanceFactor
              sourceTranslate) := by
      simpa [physicalTranslate, sourceTranslate] using
        retainedFinalPhysicalTranslation_eq_refinedSourceTranslation
          formula relativeTranslate
    rw [physicalTranslateEq]
    dsimp [fallbackCenter]
    rw [cell_scale_add, cell_scale_add]
  have positionedCentersEqual :
      retainedDirectSourcePositionedFanCenterAt
          choice.origin choice.kind choice.index = translatedCenter := by
    simpa [translatedCenter, translatedRawRoute, sourceTranslate, rawRoute] using
      retainedFinalDirectTranslatedFallback_positionedFanCenters_eq_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        relativeTranslate centersEqual
  have fallbackSpoke :=
    retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  calc
    translatePolyline physicalTranslate
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            (angularOccurrenceOrder
              ((finalCoordinatedSource formula).scale
                retainedAngularFanSourceClearanceFactor).erase
              (PositionedPeriodicCNF.scaleIncidenceRoutes
                retainedAngularFanSourceClearanceFactor
                (finalCoordinatedSourceRoutes formula)))
            (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
            fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)) =
        translatePolyline physicalTranslate
          (retainedTerminalFanFigure7SpokeRouteAt
            fallbackCenter fallbackSlot) := by
              rw [fallbackSpoke]
    _ = retainedTerminalFanFigure7SpokeRouteAt
          (Cell.add physicalTranslate fallbackCenter) fallbackSlot :=
      translatePolyline_retainedTerminalFanFigure7SpokeRouteAt
        physicalTranslate fallbackCenter fallbackSlot
    _ = retainedTerminalFanFigure7SpokeRouteAt
          translatedCenter fallbackSlot := by rw [translatedCenterEq]
    _ = retainedTerminalFanFigure7SpokeRouteAt
          (retainedDirectSourcePositionedFanCenterAt
            choice.origin choice.kind choice.index) fallbackSlot := by
      rw [positionedCentersEqual]
    _ = choice.figure7Spoke fallbackSlot :=
      (retainedDirectSourceRouteChoice_figure7Spoke_eq_spokeRouteAt
        choice fallbackSlot).symm

/-- For a same-center aligned mixed pair, the direct prefix and direct suffix
both strictly avoid the translated fallback suffix. -/
theorem
    retainedFinalCoordinatedAlignedDirectOccurrencePieces_strictlyAvoid_translatedFallbackSuffix_of_sameCenter
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
    (directAligned : choice.sourceSegment.IsAxisAligned)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            fallbackClause fallbackLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let directSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex
    let physicalTranslate :=
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate
    let fallbackSuffix :=
      translatePolyline physicalTranslate
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
            fallbackLiteral fallbackClauseIndex fallbackLiteralIndex))
    RoutesStrictlyAvoidEachOther
        (choice.completeRoute directSlot) fallbackSuffix ∧
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement
            (angularOccurrenceOrder source.erase routes)
            (directClause.scale retainedAngularFanSourceClearanceFactor)
            directLiteral directClauseIndex directLiteralIndex))
        fallbackSuffix := by
  dsimp only
  let directSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula directLiteral directClauseIndex directLiteralIndex
  let fallbackSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula fallbackLiteral fallbackClauseIndex fallbackLiteralIndex
  let fallbackSuffix :=
    translatePolyline
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate)
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)
          (angularOccurrenceOrder
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor).erase
            (PositionedPeriodicCNF.scaleIncidenceRoutes
              retainedAngularFanSourceClearanceFactor
              (finalCoordinatedSourceRoutes formula)))
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex))
  have angularOrder :=
    retainedFinalDirectFallback_strictAngularOrderCompatible_of_center_eq_translated_of_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember choiceLookup
      fallbackChoiceNone directAligned relativeTranslate
      relativeTranslateNonzero centersEqual
  have slotsDifferent : directSlot ≠ fallbackSlot :=
    directFallbackStrictAngularOrderCompatible_slots_ne
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula fallbackClauseIndex fallbackLiteralIndex))).1
      directSlot fallbackSlot (by simpa [directSlot, fallbackSlot] using angularOrder)
  have fallbackSuffixEq :
      fallbackSuffix = choice.figure7Spoke fallbackSlot := by
    simpa [fallbackSuffix, fallbackSlot] using
      retainedFinalTranslatedFallbackOccurrenceSuffix_eq_directFigure7Spoke_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember choiceLookup
        relativeTranslate centersEqual
  have directSuffixEq :=
    retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice directClauseMember directLiteralMember
      choiceLookup
  dsimp only at directSuffixEq
  constructor
  · have prefixAvoid :=
      choice.completeRoute_strictlyAvoid_otherFigure7Spoke
        directSlot fallbackSlot slotsDifferent
    rw [← fallbackSuffixEq] at prefixAvoid
    simpa [directSlot, fallbackSuffix] using prefixAvoid
  · have spokeAvoid :=
      retainedDirectSourceRouteChoice_figure7Spokes_strictlyAvoid
        choice directSlot fallbackSlot slotsDifferent
    rw [directSuffixEq, ← fallbackSuffixEq] at spokeAvoid
    simpa [directSlot, fallbackSuffix,
      finalCoordinatedSource, finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes] using spokeAvoid

end PeriodicOrthocrossing
end LeanTrominoes
