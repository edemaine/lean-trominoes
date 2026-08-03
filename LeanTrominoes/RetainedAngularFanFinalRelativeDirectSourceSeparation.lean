import LeanTrominoes.RetainedAngularFanFinalRelativeDirectSourceModels
import LeanTrominoes.RetainedAngularFanFinalDirectSourceCrossClauseSeparation

/-!
# Relative separation of final direct copied-source routes

Successful direct-source choices reduce translated public routes to the
finite Figure 7 atlas.  Distinct component macrocells have disjoint route
envelopes.  When the translated components coincide, strict separation of
the inherited retained-source prefixes is enough to select one of the
contact-free finite atlas configurations.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- A successful direct component remains the same component kind after a
drawing-period translation of its macrocell center. -/
theorem RetainedFinalDirectSourceCenterKind.periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {kind : RetainedDirectClauseKind}
    {center : Cell}
    (data :
      RetainedFinalDirectSourceCenterKind formula kind center)
    (relativeTranslate : Cell) :
    RetainedFinalDirectSourceCenterKind formula kind
      (Cell.add center
        ((PeriodicOrthocrossing.drawing formula.incidenceGraph)
          |>.periodTranslation relativeTranslate)) := by
  cases data with
  | crossover clauseIndex crossing shift crossingMember =>
      have shifted :=
        RetainedFinalDirectSourceCenterKind.crossover
          (formula := formula) clauseIndex crossing
          (Cell.add shift relativeTranslate) crossingMember
      rw [PeriodicOrthocrossing.periodTranslation_add] at shifted
      simpa only [Cell.add, add_assoc] using shifted
  | duplicator arm clauseIndex site shift siteMember =>
      have shifted :=
        RetainedFinalDirectSourceCenterKind.duplicator
          (formula := formula) arm clauseIndex site
          (Cell.add shift relativeTranslate) siteMember
      rw [PeriodicOrthocrossing.periodTranslation_add] at shifted
      simpa only [Cell.add, add_assoc] using shifted
  | routedClause site shift siteMember =>
      have shifted :=
        RetainedFinalDirectSourceCenterKind.routedClause
          (formula := formula) site
          (Cell.add shift relativeTranslate) siteMember
      rw [PeriodicOrthocrossing.periodTranslation_add] at shifted
      simpa only [Cell.add, add_assoc] using shifted

/-- Translating a successful direct choice by the retained-source period
translation produces valid origin data for the translated component. -/
theorem retainedFinalDirectSourceRouteChoice_translateOrigin_originData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (choice : RetainedDirectSourceRouteChoice)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    (relativeTranslate : Cell) :
    Nonempty
      (RetainedFinalDirectSourceOriginData formula
        (choice.translateOrigin
          ((PeriodicOrthocrossing.finalCoordinatedPlacement formula)
            |>.translation relativeTranslate))) := by
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula clauseIndex literalIndex choice choiceLookup with
    ⟨data⟩
  let translatedCenter :=
    Cell.add data.center
      ((PeriodicOrthocrossing.drawing formula.incidenceGraph)
        |>.periodTranslation relativeTranslate)
  refine Nonempty.intro {
    center := translatedCenter
    originEq := ?_
    centerKind := data.centerKind.periodTranslate relativeTranslate
  }
  rw [show
      (PeriodicOrthocrossing.finalCoordinatedPlacement formula).translation
          relativeTranslate =
        PeriodicOrthocrossing.carrierMacroPeriodTranslation
          formula.incidenceGraph relativeTranslate by
      simpa only [PeriodicOrthocrossing.finalCoordinatedPlacement] using
        PeriodicOrthocrossing.retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
          formula relativeTranslate]
  rw [PeriodicOrthocrossing.carrierMacroPeriodTranslation_eq_scale_periodTranslation]
  simp only [RetainedDirectSourceRouteChoice.translateOrigin]
  rw [data.originEq]
  rcases centerEq : data.center with ⟨centerX, centerY⟩
  rcases translateEq :
      (PeriodicOrthocrossing.drawing
        formula.incidenceGraph).periodTranslation relativeTranslate with
    ⟨translateX, translateY⟩
  simp [translatedCenter,
    centerEq, translateEq,
    Cell.add, Cell.scale, planarMacroScale]
  constructor <;> ring

/-- At a common component origin, two distinct local clauses in the same
component family have contact-free complete Figure 7 replacements.  Equal
targets use the semantic angular order; different targets use the finite
cross-clause envelope certificates. -/
theorem
    retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_sameFamily :
    ∀ (firstKind secondKind : RetainedDirectClauseKind)
      (firstIndex :
        Fin (retainedDirectSourcePrefixChoices firstKind).length)
      (secondIndex :
        Fin (retainedDirectSourcePrefixChoices secondKind).length)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstKind.SameFamily secondKind →
        (retainedDirectSourceLocalChoice
            firstKind firstIndex).sourceSegment.start ≠
          (retainedDirectSourceLocalChoice
            secondKind secondIndex).sourceSegment.start →
        ((retainedDirectSourceLocalChoice
              firstKind firstIndex).sourceSegment.finish =
            (retainedDirectSourceLocalChoice
              secondKind secondIndex).sourceSegment.finish ∧
            RetainedDirectSourceRouteChoice.AngularOrderCompatible
              (retainedDirectSourceLocalChoice firstKind firstIndex)
              (retainedDirectSourceLocalChoice secondKind secondIndex)
              firstSlot secondSlot) ∨
          (retainedDirectSourceLocalChoice
              firstKind firstIndex).sourceSegment.finish ≠
            (retainedDirectSourceLocalChoice
              secondKind secondIndex).sourceSegment.finish →
        RoutesStrictlyAvoidEachOther
          ((retainedDirectSourceLocalChoice firstKind firstIndex)
            |>.completeFigure7Route firstSlot)
          ((retainedDirectSourceLocalChoice secondKind secondIndex)
            |>.completeFigure7Route secondSlot) := by
  intro firstKind secondKind firstIndex secondIndex
    firstSlot secondSlot sameFamily startsDifferent finishCase
  cases firstKind with
  | crossover firstClauseIndex =>
      cases secondKind with
      | crossover secondClauseIndex =>
          by_cases clausesEqual : firstClauseIndex = secondClauseIndex
          · subst secondClauseIndex
            exfalso
            apply startsDifferent
            simpa [retainedDirectSourceLocalChoice,
              RetainedDirectSourceRouteChoice.sourceSegment,
              Cell.add] using
              retainedDirectSourceLocalRouteAt_headD_eq_of_sameKind
                (.crossover firstClauseIndex) firstIndex secondIndex
          · rcases finishCase with
              ⟨finishesEqual, angularOrder⟩ | finishesDifferent
            · exact
                retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid
                  firstClauseIndex secondClauseIndex
                  firstIndex secondIndex firstSlot secondSlot
                  clausesEqual finishesEqual angularOrder
            · exact
                retainedDirectSourceCrossoverCrossClauseOtherTarget_strictlyAvoid
                  firstClauseIndex secondClauseIndex
                  firstIndex secondIndex firstSlot secondSlot
                  clausesEqual finishesDifferent
      | duplicator => simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | routedClause => simp [RetainedDirectClauseKind.SameFamily] at sameFamily
  | duplicator firstArm firstClauseIndex =>
      cases secondKind with
      | crossover => simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | duplicator secondArm secondClauseIndex =>
          by_cases branchesEqual :
              (firstArm, firstClauseIndex) =
                (secondArm, secondClauseIndex)
          · cases branchesEqual
            exfalso
            apply startsDifferent
            simpa [retainedDirectSourceLocalChoice,
              RetainedDirectSourceRouteChoice.sourceSegment,
              Cell.add] using
              retainedDirectSourceLocalRouteAt_headD_eq_of_sameKind
                (.duplicator firstArm firstClauseIndex)
                firstIndex secondIndex
          · rcases finishCase with
              ⟨finishesEqual, angularOrder⟩ | finishesDifferent
            · exact
                retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid
                  firstArm secondArm firstClauseIndex secondClauseIndex
                  firstIndex secondIndex firstSlot secondSlot
                  branchesEqual finishesEqual angularOrder
            · exact
                retainedDirectSourceDuplicatorCrossClauseOtherTarget_strictlyAvoid
                  firstArm secondArm firstClauseIndex secondClauseIndex
                  firstIndex secondIndex firstSlot secondSlot
                  branchesEqual finishesDifferent
      | routedClause => simp [RetainedDirectClauseKind.SameFamily] at sameFamily
  | routedClause =>
      cases secondKind with
      | crossover => simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | duplicator => simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | routedClause =>
          exfalso
          apply startsDifferent
          simpa [retainedDirectSourceLocalChoice,
            RetainedDirectSourceRouteChoice.sourceSegment,
            Cell.add] using
            retainedDirectSourceLocalRouteAt_headD_eq_of_sameKind
              .routedClause firstIndex secondIndex

/-- The common-origin local theorem in positioned-choice coordinates. -/
theorem
    RetainedDirectSourceRouteChoice.completeFigure7Routes_strictlyAvoid_of_sameOrigin_sameFamily
    (first second : RetainedDirectSourceRouteChoice)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (originsEqual : first.origin = second.origin)
    (sameFamily : first.kind.SameFamily second.kind)
    (startsDifferent :
      first.sourceSegment.start ≠ second.sourceSegment.start)
    (finishCase :
      (first.sourceSegment.finish = second.sourceSegment.finish ∧
          first.AngularOrderCompatible
            second firstSlot secondSlot) ∨
        first.sourceSegment.finish ≠ second.sourceSegment.finish) :
    RoutesStrictlyAvoidEachOther
      (first.completeFigure7Route firstSlot)
      (second.completeFigure7Route secondSlot) := by
  rcases first with ⟨firstOrigin, firstKind, firstIndex⟩
  rcases second with ⟨secondOrigin, secondKind, secondIndex⟩
  simp only at originsEqual
  subst secondOrigin
  have localStartsDifferent :
      (retainedDirectSourceLocalChoice
          firstKind firstIndex).sourceSegment.start ≠
        (retainedDirectSourceLocalChoice
          secondKind secondIndex).sourceSegment.start := by
    intro localEqual
    apply startsDifferent
    simpa [RetainedDirectSourceRouteChoice.sourceSegment,
      retainedDirectSourceLocalChoice, Cell.add] using
      congrArg (Cell.add firstOrigin) localEqual
  have localFinishCase :
      ((retainedDirectSourceLocalChoice
            firstKind firstIndex).sourceSegment.finish =
          (retainedDirectSourceLocalChoice
            secondKind secondIndex).sourceSegment.finish ∧
          RetainedDirectSourceRouteChoice.AngularOrderCompatible
            (retainedDirectSourceLocalChoice firstKind firstIndex)
            (retainedDirectSourceLocalChoice secondKind secondIndex)
            firstSlot secondSlot) ∨
        (retainedDirectSourceLocalChoice
            firstKind firstIndex).sourceSegment.finish ≠
          (retainedDirectSourceLocalChoice
            secondKind secondIndex).sourceSegment.finish := by
    rcases finishCase with
        ⟨positionedFinishesEqual, angularOrder⟩ |
        positionedFinishesDifferent
    · left
      constructor
      · apply Cell.add_left_injective firstOrigin
        simpa [RetainedDirectSourceRouteChoice.sourceSegment,
          retainedDirectSourceLocalChoice, Cell.add] using
          positionedFinishesEqual
      · simpa [RetainedDirectSourceRouteChoice.AngularOrderCompatible,
          retainedDirectSourceLocalChoice] using angularOrder
    · right
      intro localEqual
      apply positionedFinishesDifferent
      simpa [RetainedDirectSourceRouteChoice.sourceSegment,
        retainedDirectSourceLocalChoice, Cell.add] using
        congrArg (Cell.add firstOrigin) localEqual
  exact
    retainedDirectSourceSameOriginCompleteFigure7Routes_strictlyAvoid_of_local
      firstOrigin firstKind secondKind firstIndex secondIndex
      firstSlot secondSlot
      (retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_sameFamily
        firstKind secondKind firstIndex secondIndex
        firstSlot secondSlot sameFamily
        localStartsDifferent localFinishCase)

end PeriodicEightOccurrenceSplit

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- No point is fixed by a nonzero lattice translation of a positive-period
placement. -/
theorem PeriodicVariablePlacement.point_ne_add_translation_of_nonzero
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period)
    (point relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    point ≠
      Cell.add point (placement.translation relativeTranslate) := by
  rcases point with ⟨pointX, pointY⟩
  rcases relativeTranslate with ⟨translateX, translateY⟩
  intro equal
  apply relativeTranslateNonzero
  simp only [PeriodicVariablePlacement.translation,
    Cell.add, Cell.scale, Prod.mk.injEq] at equal ⊢
  constructor <;> nlinarith

/-- Equality with a translated canonical literal position still identifies
the two fundamental-square wrapped atom representatives. -/
theorem retainedFinalCanonicalLiteralPosition_eq_translated_imp_atoms_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
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
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    firstLiteral.atom = secondLiteral.atom := by
  let placement := finalCoordinatedPlacement formula
  let shiftedSecondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) := {
    atom := secondLiteral.atom
    offset := Cell.add secondLiteral.offset relativeTranslate
    value := secondLiteral.value
  }
  have shiftedPositionsEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement secondClause shiftedSecondLiteral := by
    rcases firstPositionEq : placement.position firstLiteral.atom with
      ⟨firstX, firstY⟩
    rcases secondPositionEq : placement.position secondLiteral.atom with
      ⟨secondX, secondY⟩
    rcases firstOffsetEq : firstLiteral.offset with
      ⟨firstOffsetX, firstOffsetY⟩
    rcases secondOffsetEq : secondLiteral.offset with
      ⟨secondOffsetX, secondOffsetY⟩
    rcases relativeTranslate with ⟨relativeX, relativeY⟩
    simp only [placement, shiftedSecondLiteral,
      PositionedPeriodicCNF.canonicalLiteralPosition,
      PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale,
      firstPositionEq, secondPositionEq,
      firstOffsetEq, secondOffsetEq, Prod.mk.injEq]
      at positionsEqual ⊢
    constructor
    · linear_combination positionsEqual.1
    · linear_combination positionsEqual.2
  have firstBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula firstLiteral.atom
  have secondBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula secondLiteral.atom
  have positionEq :=
    PositionedPeriodicCNF.canonicalLiteralPosition_eq_imp_position_eq
      placement
      (by
        simpa [placement, finalCoordinatedPlacement,
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
          wrappedDrawingPeriodicPlanarSATPlacement] using
          drawingPeriodicPlanarSATPlacement_period_pos formula)
      firstClause secondClause firstLiteral shiftedSecondLiteral
      ⟨firstBounds.1.le, firstBounds.2.1,
        firstBounds.2.2.1.le, firstBounds.2.2.2⟩
      ⟨secondBounds.1.le, secondBounds.2.1,
        secondBounds.2.2.1.le, secondBounds.2.2.2⟩
      shiftedPositionsEqual
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have firstAtomMember :
      firstLiteral.atom ∈
        (finalCoordinatedSource formula).erase.variableOccurrences :=
    atom_mem_variableOccurrences_of_positioned_members
      (finalCoordinatedSource formula)
      firstClauseMember firstLiteralMember
  have secondAtomMember :
      secondLiteral.atom ∈
        (finalCoordinatedSource formula).erase.variableOccurrences :=
    atom_mem_variableOccurrences_of_positioned_members
      (finalCoordinatedSource formula)
      secondClauseMember secondLiteralMember
  have firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula firstLiteral.atom.original :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      (by simpa [finalCoordinatedSource] using firstAtomMember)
  have secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula secondLiteral.atom.original :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      (by simpa [finalCoordinatedSource] using secondAtomMember)
  exact
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_injective_of_valid
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      firstValid secondValid
      (by simpa [placement, finalCoordinatedPlacement] using positionEq)

/-- Two successful direct copied-source routes are strictly separated after
any nonzero relative period translation. -/
theorem
    retainedFinalDirectSourceCompleteFigure7Routes_strictlyAvoid_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
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
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    let sourceTranslate :=
      (finalCoordinatedPlacement formula).translation relativeTranslate
    let translatedSecondChoice :=
      secondChoice.translateOrigin sourceTranslate
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    RoutesStrictlyAvoidEachOther
      (firstChoice.completeFigure7Route firstSlot)
      (translatedSecondChoice.completeFigure7Route secondSlot) := by
  dsimp only
  let placement := finalCoordinatedPlacement formula
  let sourceTranslate := placement.translation relativeTranslate
  let translatedSecondChoice :=
    secondChoice.translateOrigin sourceTranslate
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula firstClauseIndex firstLiteralIndex
      firstChoice firstChoiceLookup with
    ⟨firstData⟩
  rcases
      retainedFinalDirectSourceRouteChoice_translateOrigin_originData
        formula secondClauseIndex secondLiteralIndex
        secondChoice secondChoiceLookup relativeTranslate with
    ⟨translatedSecondData⟩
  change RoutesStrictlyAvoidEachOther
      (firstChoice.completeFigure7Route firstSlot)
      (translatedSecondChoice.completeFigure7Route secondSlot)
  by_cases originsEqual :
      firstChoice.origin = translatedSecondChoice.origin
  · have centersEqual :
        firstData.center = translatedSecondData.center := by
      apply Cell.scale_injective
        (show (planarMacroScale : Int) ≠ 0 by
          simp [planarMacroScale])
      rw [← firstData.originEq, ← translatedSecondData.originEq]
      exact originsEqual
    let sourceCertificate :=
      retainedPlanarSATCertificate formula
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
    have sameFamily :
        firstChoice.kind.SameFamily translatedSecondChoice.kind :=
      retainedFinalDirectSourceCenterKinds_sameFamily
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        firstData.centerKind translatedSecondData.centerKind centersEqual
    have firstStart :=
      retainedFinalDirectSourceRouteChoice_sourceSegment_start
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstChoice
        firstClauseMember firstLiteralMember firstChoiceLookup
    have secondStart :=
      retainedFinalDirectSourceRouteChoice_sourceSegment_start
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondChoice
        secondClauseMember secondLiteralMember secondChoiceLookup
    have translatedSegment :=
      RetainedDirectSourceRouteChoice.translateOrigin_sourceSegment
        secondChoice sourceTranslate
    have translatedStart :
        translatedSecondChoice.sourceSegment.start =
          Cell.add sourceTranslate secondChoice.sourceSegment.start := by
      rw [show translatedSecondChoice.sourceSegment =
          GridSegment.translate sourceTranslate secondChoice.sourceSegment by
        simpa [translatedSecondChoice] using translatedSegment]
      rfl
    have translatedFinish :
        translatedSecondChoice.sourceSegment.finish =
          Cell.add sourceTranslate secondChoice.sourceSegment.finish := by
      rw [show translatedSecondChoice.sourceSegment =
          GridSegment.translate sourceTranslate secondChoice.sourceSegment by
        simpa [translatedSecondChoice] using translatedSegment]
      rfl
    have startsDifferent :
        firstChoice.sourceSegment.start ≠
          translatedSecondChoice.sourceSegment.start := by
      have clauseStartsDifferent :=
        finalCoordinatedCanonicalClausePositions_ne_translated_of_nonzero
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember secondClauseMember
          relativeTranslate relativeTranslateNonzero
      intro startsEqual
      apply clauseStartsDifferent
      calc
        PositionedPeriodicCNF.canonicalClausePosition
            (finalCoordinatedPlacement formula) firstClause =
            firstChoice.sourceSegment.start := firstStart.symm
        _ = translatedSecondChoice.sourceSegment.start := startsEqual
        _ = Cell.add sourceTranslate
              secondChoice.sourceSegment.start := translatedStart
        _ = Cell.add secondChoice.sourceSegment.start
              sourceTranslate := by
            rcases sourceTranslate with ⟨translateX, translateY⟩
            rcases secondChoice.sourceSegment.start with
              ⟨startX, startY⟩
            simp [Cell.add, add_comm]
        _ = Cell.add
              (PositionedPeriodicCNF.canonicalClausePosition
                (finalCoordinatedPlacement formula) secondClause)
              ((finalCoordinatedPlacement formula).translation
                relativeTranslate) := by
            rw [secondStart]
    have finishCase :
        (firstChoice.sourceSegment.finish =
            translatedSecondChoice.sourceSegment.finish ∧
          firstChoice.AngularOrderCompatible
            translatedSecondChoice firstSlot secondSlot) ∨
        firstChoice.sourceSegment.finish ≠
          translatedSecondChoice.sourceSegment.finish := by
      by_cases finishesEqual :
          firstChoice.sourceSegment.finish =
            translatedSecondChoice.sourceSegment.finish
      · left
        refine ⟨finishesEqual, ?_⟩
        have firstFinish :=
          retainedFinalDirectSourceRouteChoice_sourceSegment_finish
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty firstChoice
            firstClauseMember firstLiteralMember firstChoiceLookup
        have secondFinish :=
          retainedFinalDirectSourceRouteChoice_sourceSegment_finish
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty secondChoice
            secondClauseMember secondLiteralMember secondChoiceLookup
        have targetPositionsEqual :
            PositionedPeriodicCNF.canonicalLiteralPosition
                placement firstClause firstLiteral =
              Cell.add
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  placement secondClause secondLiteral)
                (placement.translation relativeTranslate) := by
          calc
            PositionedPeriodicCNF.canonicalLiteralPosition
                placement firstClause firstLiteral =
                firstChoice.sourceSegment.finish := by
              simpa [placement] using firstFinish.symm
            _ = translatedSecondChoice.sourceSegment.finish :=
              finishesEqual
            _ = Cell.add sourceTranslate
                  secondChoice.sourceSegment.finish := translatedFinish
            _ = Cell.add secondChoice.sourceSegment.finish
                  sourceTranslate := by
              rcases sourceTranslate with ⟨translateX, translateY⟩
              rcases secondChoice.sourceSegment.finish with
                ⟨finishX, finishY⟩
              simp [Cell.add, add_comm]
            _ = Cell.add
                  (PositionedPeriodicCNF.canonicalLiteralPosition
                    placement secondClause secondLiteral)
                  (placement.translation relativeTranslate) := by
              rw [secondFinish]
        have atomsEqual :=
          retainedFinalCanonicalLiteralPosition_eq_translated_imp_atoms_eq
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            firstClauseMember secondClauseMember
            firstLiteralMember secondLiteralMember
            relativeTranslate
            (by simpa [placement] using targetPositionsEqual)
        have occurrenceKeysDifferent :
            (firstClauseIndex, firstLiteralIndex) ≠
              (secondClauseIndex, secondLiteralIndex) := by
          intro keysEqual
          have clauseIndexEqual :
              firstClauseIndex = secondClauseIndex :=
            congrArg Prod.fst keysEqual
          have literalIndexEqual :
              firstLiteralIndex = secondLiteralIndex :=
            congrArg Prod.snd keysEqual
          have clausesEqual : firstClause = secondClause := by
            have firstLookup :=
              (List.mem_zipIdx_iff_getElem?).mp firstClauseMember
            have secondLookup :=
              (List.mem_zipIdx_iff_getElem?).mp secondClauseMember
            have : some firstClause = some secondClause := by
              rw [← firstLookup, ← secondLookup, clauseIndexEqual]
            exact Option.some.inj this
          subst secondClause
          have literalsEqual : firstLiteral = secondLiteral := by
            have firstLookup :=
              (List.mem_zipIdx_iff_getElem?).mp firstLiteralMember
            have secondLookup :=
              (List.mem_zipIdx_iff_getElem?).mp secondLiteralMember
            have : some firstLiteral = some secondLiteral := by
              rw [← firstLookup, ← secondLookup, literalIndexEqual]
            exact Option.some.inj this
          subst secondLiteral
          exact
            (PeriodicVariablePlacement.point_ne_add_translation_of_nonzero
              placement
              (by
                simpa [placement, finalCoordinatedPlacement,
                  retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
                  wrappedDrawingPeriodicPlanarSATPlacement] using
                  drawingPeriodicPlanarSATPlacement_period_pos formula)
              (PositionedPeriodicCNF.canonicalLiteralPosition
                placement firstClause firstLiteral)
              relativeTranslate relativeTranslateNonzero)
              targetPositionsEqual
        have angularOrder :=
          retainedFinalDirectSourceRouteChoices_angularOrderCompatible
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty firstChoice secondChoice
            firstClauseMember secondClauseMember
            firstLiteralMember secondLiteralMember
            firstChoiceLookup secondChoiceLookup
            atomsEqual occurrenceKeysDifferent
        simpa [translatedSecondChoice,
          RetainedDirectSourceRouteChoice.translateOrigin,
          RetainedDirectSourceRouteChoice.AngularOrderCompatible,
          firstSlot, secondSlot] using angularOrder
      · exact Or.inr finishesEqual
    exact
      firstChoice.completeFigure7Routes_strictlyAvoid_of_sameOrigin_sameFamily
        translatedSecondChoice firstSlot secondSlot
        originsEqual sameFamily startsDifferent finishCase
  · have centersDifferent :
        firstData.center ≠ translatedSecondData.center := by
      intro centersEqual
      apply originsEqual
      rw [firstData.originEq, translatedSecondData.originEq,
        centersEqual]
    exact
      firstChoice.completeFigure7Routes_strictlyAvoid_of_sourceRectanglesSeparated
        translatedSecondChoice firstSlot secondSlot
        (firstChoice.sourceRectanglesSeparated_of_originCenters_ne
          translatedSecondChoice
          firstData.center translatedSecondData.center
          firstData.originEq translatedSecondData.originEq
          centersDifferent)

/-- Public coordinated direct routes inherit the nonzero-period strict
separation theorem through their exact translated atlas models. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_direct_strictlyAvoid_translated_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
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
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0)) :
    RoutesStrictlyAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula secondClauseIndex secondLiteralIndex)) := by
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_eq_completeFigure7Route_of_choice_some
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice
      firstClauseMember firstLiteralMember firstChoiceLookup]
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_translate_of_choice_some
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondChoice
      secondClauseMember secondLiteralMember secondChoiceLookup
      relativeTranslate]
  exact
    retainedFinalDirectSourceCompleteFigure7Routes_strictlyAvoid_translated_of_nonzero
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice secondChoice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceLookup secondChoiceLookup
      relativeTranslate relativeTranslateNonzero

end PeriodicOrthocrossing
end LeanTrominoes
