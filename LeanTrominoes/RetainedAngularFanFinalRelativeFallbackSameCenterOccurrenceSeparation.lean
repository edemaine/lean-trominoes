import LeanTrominoes.RetainedAngularFanFinalRelativeFallbackSameCenterBoundarySeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeMixedSameCenterFallbackSpokeSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedPublicSeparation

/-!
# Same-center translated fallback occurrence separation

The selected fallback boundary is joined to its unchanged Figure 7 spoke.
At a shared translated variable center, different occurrence slots separate
each boundary from the opposite spoke and separate the two spokes themselves.
Together with boundary separation, the four component certificates assemble
into separation of the complete occurrence routes.
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

/-- The unchanged Figure 7 suffix attached to a final fallback boundary. -/
def retainedFinalFallbackOccurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat) : List Cell :=
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
  scalePolyline retainedTerminalFanRoutingRefinement
    (angularOccurrenceSuffix placement
      (angularOccurrenceOrder source.erase routes)
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal clauseIndex literalIndex)

/-- The same occurrence suffix after a physical period translation. -/
def retainedFinalTranslatedFallbackOccurrenceSuffix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable))
    (clauseIndex literalIndex : Nat)
    (relativeTranslate : Cell) : List Cell :=
  translatePolyline
    ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate)
    (retainedFinalFallbackOccurrenceSuffix
      formula clause literal clauseIndex literalIndex)

/-- The fully refined canonical fan center of one retained occurrence. -/
def retainedFinalFallbackCanonicalFanCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) : Cell :=
  Cell.scale retainedTerminalFanTotalRefinement
    (Cell.scale retainedAngularFanSourceClearanceFactor
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (finalCoordinatedPlacement formula) clause literal))

/-- Equality of canonical targets across a period shift becomes equality of
the first refined fan center and the translated second refined fan center. -/
theorem retainedFinalFallbackCanonicalFanCenter_eq_add_translated_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    (relativeTranslate : Cell)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    retainedFinalFallbackCanonicalFanCenter
        formula firstClause firstLiteral =
      Cell.add
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedFinalFallbackCanonicalFanCenter
          formula secondClause secondLiteral) := by
  unfold retainedFinalFallbackCanonicalFanCenter
  rw [centersEqual,
    retainedFinalPhysicalTranslation_eq_refinedSourceTranslation]
  rcases (finalCoordinatedPlacement formula).translation
      relativeTranslate with ⟨translateX, translateY⟩
  rcases PositionedPeriodicCNF.canonicalLiteralPosition
      (finalCoordinatedPlacement formula)
      secondClause secondLiteral with ⟨centerX, centerY⟩
  simp [Cell.add, Cell.scale]
  constructor <;> ring

/-- The first selected fallback boundary avoids the translated Figure 7
suffix of the second occurrence at their shared physical fan center. -/
theorem
    retainedFinalFallbackBoundaryPrefix_strictlyAvoids_translatedOccurrenceSuffix_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedFallbackBoundaryPrefix
        formula firstLiteral firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackOccurrenceSuffix
        formula secondClause secondLiteral
        secondClauseIndex secondLiteralIndex relativeTranslate) := by
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let firstCenter :=
    retainedFinalFallbackCanonicalFanCenter
      formula firstClause firstLiteral
  let secondCenter :=
    retainedFinalFallbackCanonicalFanCenter
      formula secondClause secondLiteral
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  have slotsDifferent : firstSlot ≠ secondSlot := by
    simpa [firstSlot, secondSlot] using
      retainedFinalCoordinatedOccurrenceSlots_ne_of_center_eq_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero centersEqual
  have refinedCentersEqual :
      firstCenter = Cell.add physicalTranslate secondCenter := by
    simpa [firstCenter, secondCenter, physicalTranslate] using
      retainedFinalFallbackCanonicalFanCenter_eq_add_translated_of_sameCenter
        formula relativeTranslate centersEqual
  have secondSpokeEq :
      retainedTerminalFanFigure7SpokeRouteAt secondCenter secondSlot =
        retainedFinalFallbackOccurrenceSuffix
          formula secondClause secondLiteral
          secondClauseIndex secondLiteralIndex := by
    simpa [retainedFinalFallbackOccurrenceSuffix,
      retainedFinalFallbackCanonicalFanCenter,
      secondCenter, secondSlot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSpokeEq :
      retainedFinalTranslatedFallbackOccurrenceSuffix
          formula secondClause secondLiteral
          secondClauseIndex secondLiteralIndex relativeTranslate =
        retainedTerminalFanFigure7SpokeRouteAt firstCenter secondSlot := by
    rw [retainedFinalTranslatedFallbackOccurrenceSuffix, ← secondSpokeEq,
      translatePolyline_retainedTerminalFanFigure7SpokeRouteAt,
      ← refinedCentersEqual]
  have localAvoid :=
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_otherFigure7SpokeRouteAt
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
      firstChoiceNone secondSlot slotsDifferent
  rw [translatedSpokeEq]
  simpa [firstCenter, retainedFinalFallbackCanonicalFanCenter] using
    localAvoid

/-- The first occurrence's Figure 7 suffix avoids the second selected
fallback boundary after translating that boundary to the shared center. -/
theorem
    retainedFinalFallbackOccurrenceSuffix_strictlyAvoids_translatedBoundaryPrefix_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalFallbackOccurrenceSuffix
        formula firstClause firstLiteral
        firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackBoundaryPrefix
        formula secondLiteral secondClauseIndex secondLiteralIndex
        relativeTranslate) := by
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let firstCenter :=
    retainedFinalFallbackCanonicalFanCenter
      formula firstClause firstLiteral
  let secondCenter :=
    retainedFinalFallbackCanonicalFanCenter
      formula secondClause secondLiteral
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  have slotsDifferent : secondSlot ≠ firstSlot := by
    have forward : firstSlot ≠ secondSlot := by
      simpa [firstSlot, secondSlot] using
        retainedFinalCoordinatedOccurrenceSlots_ne_of_center_eq_translated_of_nonzero
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember
          relativeTranslate relativeTranslateNonzero centersEqual
    exact forward.symm
  have refinedCentersEqual :
      firstCenter = Cell.add physicalTranslate secondCenter := by
    simpa [firstCenter, secondCenter, physicalTranslate] using
      retainedFinalFallbackCanonicalFanCenter_eq_add_translated_of_sameCenter
        formula relativeTranslate centersEqual
  have firstSpokeEq :
      retainedTerminalFanFigure7SpokeRouteAt firstCenter firstSlot =
        retainedFinalFallbackOccurrenceSuffix
          formula firstClause firstLiteral
          firstClauseIndex firstLiteralIndex := by
    simpa [retainedFinalFallbackOccurrenceSuffix,
      retainedFinalFallbackCanonicalFanCenter,
      firstCenter, firstSlot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have localAvoid :=
    retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_otherFigure7SpokeRouteAt
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      secondChoiceNone firstSlot slotsDifferent
  have shifted := localAvoid.translatePolyline physicalTranslate
  have shiftedCenterEq :
      Cell.add physicalTranslate
          (Cell.scale retainedTerminalFanTotalRefinement
            (Cell.scale retainedAngularFanSourceClearanceFactor
              (PositionedPeriodicCNF.canonicalLiteralPosition
                (finalCoordinatedPlacement formula)
                secondClause secondLiteral))) = firstCenter := by
    simpa [secondCenter,
      retainedFinalFallbackCanonicalFanCenter] using
      refinedCentersEqual.symm
  rw [retainedFinalCoordinatedFallbackBoundaryPrefix_translate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      relativeTranslate,
    translatePolyline_retainedTerminalFanFigure7SpokeRouteAt,
    shiftedCenterEq, firstSpokeEq] at shifted
  simpa [secondCenter, physicalTranslate] using shifted.symm

/-- The two Figure 7 occurrence suffixes are strictly separated after the
second is translated to their shared physical fan center. -/
theorem
    retainedFinalFallbackOccurrenceSuffixes_strictlyAvoid_translated_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalFallbackOccurrenceSuffix
        formula firstClause firstLiteral
        firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackOccurrenceSuffix
        formula secondClause secondLiteral
        secondClauseIndex secondLiteralIndex relativeTranslate) := by
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  let firstCenter :=
    retainedFinalFallbackCanonicalFanCenter
      formula firstClause firstLiteral
  let secondCenter :=
    retainedFinalFallbackCanonicalFanCenter
      formula secondClause secondLiteral
  let physicalTranslate :=
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
      formula).translation relativeTranslate
  have slotsDifferent : firstSlot ≠ secondSlot := by
    simpa [firstSlot, secondSlot] using
      retainedFinalCoordinatedOccurrenceSlots_ne_of_center_eq_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero centersEqual
  have slotValuesDifferent : firstSlot.val ≠ secondSlot.val := by
    intro valuesEqual
    exact slotsDifferent (Fin.ext valuesEqual)
  have refinedCentersEqual :
      firstCenter = Cell.add physicalTranslate secondCenter := by
    simpa [firstCenter, secondCenter, physicalTranslate] using
      retainedFinalFallbackCanonicalFanCenter_eq_add_translated_of_sameCenter
        formula relativeTranslate centersEqual
  have firstSpokeEq :
      retainedTerminalFanFigure7SpokeRouteAt firstCenter firstSlot =
        retainedFinalFallbackOccurrenceSuffix
          formula firstClause firstLiteral
          firstClauseIndex firstLiteralIndex := by
    simpa [retainedFinalFallbackOccurrenceSuffix,
      retainedFinalFallbackCanonicalFanCenter,
      firstCenter, firstSlot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondSpokeEq :
      retainedTerminalFanFigure7SpokeRouteAt secondCenter secondSlot =
        retainedFinalFallbackOccurrenceSuffix
          formula secondClause secondLiteral
          secondClauseIndex secondLiteralIndex := by
    simpa [retainedFinalFallbackOccurrenceSuffix,
      retainedFinalFallbackCanonicalFanCenter,
      secondCenter, secondSlot] using
      retainedFinalFallbackFigure7SpokeRouteAt_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSpokeEq :
      retainedFinalTranslatedFallbackOccurrenceSuffix
          formula secondClause secondLiteral
          secondClauseIndex secondLiteralIndex relativeTranslate =
        retainedTerminalFanFigure7SpokeRouteAt firstCenter secondSlot := by
    rw [retainedFinalTranslatedFallbackOccurrenceSuffix, ← secondSpokeEq,
      translatePolyline_retainedTerminalFanFigure7SpokeRouteAt,
      ← refinedCentersEqual]
  have centeredAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanFigure7SpokeRouteAt firstCenter firstSlot)
        (retainedTerminalFanFigure7SpokeRouteAt firstCenter secondSlot) := by
    rcases lt_or_gt_of_ne slotValuesDifferent with slotsLt | slotsGt
    · simpa only [retainedTerminalFanFigure7SpokeAt_eq_spokeRouteAt] using
        retainedTerminalFanFigure7SpokesAt_strictlyAvoid
          firstCenter firstSlot secondSlot slotsLt
    · have reverse :=
        (retainedTerminalFanFigure7SpokesAt_strictlyAvoid
          firstCenter secondSlot firstSlot slotsGt).symm
      simpa only [retainedTerminalFanFigure7SpokeAt_eq_spokeRouteAt] using
        reverse
  rw [← firstSpokeEq, translatedSpokeEq]
  exact centeredAvoid

/-- Two complete failed-choice occurrence routes are strictly separated at a
shared physical target across a nonzero period shift. -/
theorem
    retainedFinalFallbackOccurrenceRoute_strictlyAvoids_translated_of_sameCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula) secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalFallbackOccurrenceRoute
        formula firstClause firstLiteral
        firstClauseIndex firstLiteralIndex)
      (retainedFinalTranslatedFallbackOccurrenceRoute
        formula secondClause secondLiteral
        secondClauseIndex secondLiteralIndex relativeTranslate) := by
  let firstBoundary :=
    retainedFinalCoordinatedFallbackBoundaryPrefix
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let translatedSecondBoundary :=
    retainedFinalTranslatedFallbackBoundaryPrefix
      formula secondLiteral secondClauseIndex secondLiteralIndex
      relativeTranslate
  let firstSuffix :=
    retainedFinalFallbackOccurrenceSuffix
      formula firstClause firstLiteral
      firstClauseIndex firstLiteralIndex
  let translatedSecondSuffix :=
    retainedFinalTranslatedFallbackOccurrenceSuffix
      formula secondClause secondLiteral
      secondClauseIndex secondLiteralIndex relativeTranslate
  have boundariesAvoid :
      RoutesStrictlyAvoidEachOther firstBoundary translatedSecondBoundary := by
    simpa [firstBoundary, translatedSecondBoundary] using
      retainedFinalCoordinatedFallbackBoundaryPrefix_strictlyAvoids_translated_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        secondChoiceNone relativeTranslate relativeTranslateNonzero
        centersEqual
  have firstBoundaryAvoidSecondSuffix :
      RoutesStrictlyAvoidEachOther firstBoundary translatedSecondSuffix := by
    simpa [firstBoundary, translatedSecondSuffix] using
      retainedFinalFallbackBoundaryPrefix_strictlyAvoids_translatedOccurrenceSuffix_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember firstChoiceNone
        relativeTranslate relativeTranslateNonzero centersEqual
  have firstSuffixAvoidSecondBoundary :
      RoutesStrictlyAvoidEachOther firstSuffix translatedSecondBoundary := by
    simpa [firstSuffix, translatedSecondBoundary] using
      retainedFinalFallbackOccurrenceSuffix_strictlyAvoids_translatedBoundaryPrefix_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember secondChoiceNone
        relativeTranslate relativeTranslateNonzero centersEqual
  have suffixesAvoid :
      RoutesStrictlyAvoidEachOther firstSuffix translatedSecondSuffix := by
    simpa [firstSuffix, translatedSecondSuffix] using
      retainedFinalFallbackOccurrenceSuffixes_strictlyAvoid_translated_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember relativeTranslate
        relativeTranslateNonzero centersEqual
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
  let firstBoundaryPoint :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (angularFanBoundaryPositionAt
        placement firstLiteral.atom
        (incidenceRelativeOffset
          (firstClause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral)
        (angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          firstLiteral firstClauseIndex firstLiteralIndex))
  let secondBoundaryPoint :=
    Cell.add
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate)
      (Cell.scale retainedTerminalFanRoutingRefinement
        (angularFanBoundaryPositionAt
          placement secondLiteral.atom
          (incidenceRelativeOffset
            (secondClause.scale retainedAngularFanSourceClearanceFactor)
            secondLiteral)
          (angularOccurrenceIndex
            (angularOccurrenceOrder source.erase routes)
            secondLiteral secondClauseIndex secondLiteralIndex)))
  have firstSuffixHead : firstSuffix.head? = some firstBoundaryPoint := by
    simp [firstSuffix, retainedFinalFallbackOccurrenceSuffix,
      firstBoundaryPoint, source, placement, routes,
      angularOccurrenceSuffix_head?]
  have secondSuffixHead :
      translatedSecondSuffix.head? = some secondBoundaryPoint := by
    simp [translatedSecondSuffix,
      retainedFinalTranslatedFallbackOccurrenceSuffix,
      retainedFinalFallbackOccurrenceSuffix,
      secondBoundaryPoint, source, placement, routes,
      translatePolyline, angularOccurrenceSuffix_head?]
  have firstBoundaryJoin :=
    retainedFinalCoordinatedFallbackBoundaryPrefix_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have firstBoundaryLast :
      firstBoundary.getLast? = some firstBoundaryPoint := by
    have joinEq : firstBoundary.getLast? = firstSuffix.head? := by
      simpa [firstBoundary, firstSuffix,
        retainedFinalFallbackOccurrenceSuffix,
        source, placement, routes] using firstBoundaryJoin
    exact joinEq.trans firstSuffixHead
  have secondBoundaryJoin :=
    retainedFinalTranslatedFallbackBoundaryPrefix_boundary
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      relativeTranslate
  have secondBoundaryLast :
      translatedSecondBoundary.getLast? = some secondBoundaryPoint := by
    have joinEq :
        translatedSecondBoundary.getLast? =
          translatedSecondSuffix.head? := by
      simpa [translatedSecondBoundary, translatedSecondSuffix,
        retainedFinalTranslatedFallbackOccurrenceSuffix,
        retainedFinalFallbackOccurrenceSuffix,
        source, placement, routes] using secondBoundaryJoin
    exact joinEq.trans secondSuffixHead
  have firstOccurrenceAvoidSecondBoundary :=
    boundariesAvoid.join_left firstSuffixAvoidSecondBoundary
      firstBoundaryLast firstSuffixHead
  have firstOccurrenceAvoidSecondSuffix :=
    firstBoundaryAvoidSecondSuffix.join_left suffixesAvoid
      firstBoundaryLast firstSuffixHead
  have assembled :=
    firstOccurrenceAvoidSecondBoundary.join_right
      firstOccurrenceAvoidSecondSuffix
      secondBoundaryLast secondSuffixHead
  rw [retainedFinalFallbackOccurrenceRoute_eq_boundaryPrefix_join_suffix
    formula firstClause firstLiteral firstClauseIndex firstLiteralIndex]
  change RoutesStrictlyAvoidEachOther
    (joinAtEndpoint firstBoundary firstSuffix)
    (joinAtEndpoint translatedSecondBoundary translatedSecondSuffix)
  exact assembled

end PeriodicOrthocrossing
end LeanTrominoes
