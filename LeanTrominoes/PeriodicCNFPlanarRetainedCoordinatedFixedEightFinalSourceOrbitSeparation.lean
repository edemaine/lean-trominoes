import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalVariableOrbits
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalRouteSeparation

/-!
# Orbit separation of the final Figure Nine source macrocells

The last two gadget layers refine the retained clockwise fixed-eight source.
This file records that genuine source clauses and source variables remain
injective even modulo a whole source period.  These are the global inputs to
the finite `72 × 72` local-code collision argument.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Every variable named by one fixed nine-copy implication cycle is one
of that cycle's nine declared copies. -/
private theorem cycleClausesFor_variableOccurrence_mem_copies
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable)
    {occurrence : ThreeOccurrenceVariable Variable}
    (occurrenceMember :
      occurrence ∈
        PeriodicCNF.variableOccurrences
          (PeriodicCNF.mk
            (PeriodicEightOccurrenceSplit.cycleClausesFor atom))) :
    occurrence ∈ PeriodicEightOccurrenceSplit.copies atom := by
  simp [PeriodicEightOccurrenceSplit.cycleClausesFor,
    PeriodicEightOccurrenceSplit.copies,
    OccurrenceSplitRing.cycleVertices,
    PeriodicThreeSATThree.cycleClauses,
    PeriodicThreeSATThree.cycleFrom,
    PeriodicThreeSATThree.implicationClause,
    PeriodicCNF.variableOccurrences] at occurrenceMember ⊢
  tauto

/-- Every variable occurring in a fixed-eight split is literally one of
the nine declared copies belonging to its projected source atom. -/
private theorem formula_variableOccurrence_mem_copies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrencePorts : PeriodicEightOccurrenceSplit.OccurrencePorts)
    {occurrence : ThreeOccurrenceVariable Variable}
    (occurrenceMember :
      occurrence ∈
        (PeriodicEightOccurrenceSplit.formula
          source occurrencePorts).variableOccurrences) :
    occurrence ∈ PeriodicEightOccurrenceSplit.copies occurrence.1 := by
  change occurrence ∈
    PeriodicCNF.variableOccurrences
      (PeriodicCNF.mk
        (PeriodicEightOccurrenceSplit.occurrenceClauses
            source occurrencePorts ++
          PeriodicEightOccurrenceSplit.allCycleClauses source))
      at occurrenceMember
  rw [PeriodicThreeSATThree.variableOccurrences_append] at occurrenceMember
  rcases List.mem_append.mp occurrenceMember with
    occurrenceMember | occurrenceMember
  · rw [PeriodicEightOccurrenceSplit.occurrenceClauses_variableOccurrences]
      at occurrenceMember
    rw [PeriodicEightOccurrenceSplit.selectedCopies] at occurrenceMember
    rcases List.mem_map.mp occurrenceMember with
      ⟨taggedLiteral, taggedLiteralMember, occurrenceEqual⟩
    subst occurrence
    exact
      PeriodicEightOccurrenceSplit.selected_copy_mem_copies
        occurrencePorts taggedLiteral.1 taggedLiteral.2.1
          taggedLiteral.2.2
  · rw [PeriodicCNF.variableOccurrences, List.mem_flatMap]
      at occurrenceMember
    rcases occurrenceMember with
      ⟨clause, clauseMember, occurrenceMember⟩
    rw [PeriodicEightOccurrenceSplit.allCycleClauses,
      List.mem_flatMap] at clauseMember
    rcases clauseMember with ⟨atom, _atomMember, clauseMember⟩
    have copyMember :
        occurrence ∈ PeriodicEightOccurrenceSplit.copies atom := by
      apply cycleClausesFor_variableOccurrence_mem_copies atom
      rw [PeriodicCNF.variableOccurrences, List.mem_flatMap]
      exact ⟨clause, clauseMember, occurrenceMember⟩
    have atomEqual :=
      PeriodicEightOccurrenceSplit.copy_fst atom copyMember
    rw [atomEqual]
    exact copyMember

/-- A genuine member of the fixed nine-copy ring is recovered exactly from
the numeric index used by the positioned placement. -/
private theorem ringCopy_ringVertexOfIndex_eq_of_mem_copies
    {Variable : Type*}
    (atom : Variable)
    {occurrence : ThreeOccurrenceVariable Variable}
    (occurrenceMember :
      occurrence ∈ PeriodicEightOccurrenceSplit.copies atom) :
    PeriodicEightOccurrenceSplit.ringCopy atom
        (PeriodicEightOccurrenceSplit.ringVertexOfIndex occurrence.2.1) =
      occurrence := by
  simp [PeriodicEightOccurrenceSplit.copies,
    OccurrenceSplitRing.cycleVertices,
    PeriodicEightOccurrenceSplit.ringCopy,
    PeriodicEightOccurrenceSplit.copy,
    PeriodicEightOccurrenceSplit.portIndex] at occurrenceMember
  rcases occurrenceMember with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The nine local ring-variable coordinates are pairwise distinct. -/
private theorem ringVariablePosition_injective :
    Function.Injective OccurrenceSplitRing.ringVariablePosition := by
  intro first second equal
  cases first with
  | separator =>
      cases second with
      | separator => rfl
      | port second =>
          cases second <;>
            simp [OccurrenceSplitRing.ringVariablePosition,
              OccurrenceSplitRing.separatorPosition,
              OccurrenceSplitRing.variablePosition] at equal
  | port first =>
      cases second with
      | separator =>
          cases first <;>
            simp [OccurrenceSplitRing.ringVariablePosition,
              OccurrenceSplitRing.separatorPosition,
              OccurrenceSplitRing.variablePosition] at equal
      | port second =>
          cases first <;> cases second <;>
            simp [OccurrenceSplitRing.ringVariablePosition,
              OccurrenceSplitRing.variablePosition] at equal ⊢

/-- Subtracting the same cell from two points preserves equality in both
directions. -/
private theorem cellSub_right_injective
    (base : Cell) : Function.Injective (fun point => Cell.sub point base) := by
  intro first second equal
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases base with ⟨baseX, baseY⟩
  simp [Cell.sub, Prod.mk.injEq] at equal ⊢
  omega

/-- Local displacement of a split variable from the center of its
factor-36 source-variable macrocell. -/
private def finalSourceOccurrenceOffset
    {Variable : Type*}
    (_sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrence : ThreeOccurrenceVariable Variable) : Cell :=
  Cell.sub
    (OccurrenceSplitRing.ringVariablePosition
      (PeriodicEightOccurrenceSplit.ringVertexOfIndex occurrence.2.1))
    (12, 12)

/-- Each split variable has a radius-six local offset and the standard
factor-36 macrocell decomposition. -/
private theorem finalSourceOccurrenceOffset_data
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrence : ThreeOccurrenceVariable Variable) :
    (-6 ≤ (finalSourceOccurrenceOffset
          sourcePlacement occurrence).1 ∧
        (finalSourceOccurrenceOffset
          sourcePlacement occurrence).1 ≤ 6 ∧
      -6 ≤ (finalSourceOccurrenceOffset
          sourcePlacement occurrence).2 ∧
        (finalSourceOccurrenceOffset
          sourcePlacement occurrence).2 ≤ 6) ∧
      (PeriodicEightOccurrenceSplitPositioned.placement
          sourcePlacement).position occurrence =
        Cell.add
          (Cell.scale
            PeriodicEightOccurrenceSplitPositioned.refinementScale
            (sourcePlacement.position occurrence.1))
          (finalSourceOccurrenceOffset sourcePlacement occurrence) := by
  have localBounds :=
    OccurrenceSplitRing.ringVariablePosition_inClosedGridRectangle
      (PeriodicEightOccurrenceSplit.ringVertexOfIndex occurrence.2.1)
  constructor
  · simp only [InClosedGridRectangle] at localBounds
    simp [finalSourceOccurrenceOffset, Cell.sub] at localBounds ⊢
    omega
  · apply Prod.ext <;>
      simp [PeriodicEightOccurrenceSplitPositioned.placement,
        PeriodicEightOccurrenceSplitPositioned.occurrenceVariablePosition,
        finalSourceOccurrenceOffset,
        PeriodicEightOccurrenceSplitPositioned.macroOrigin,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring

/-- Radius-six offsets cannot hide a difference between two points of the
factor-36 source lattice. -/
private theorem finalSourceTightMacrocell_eq
    (firstBase secondBase firstOffset secondOffset : Cell)
    (firstBounds :
      -6 ≤ firstOffset.1 ∧ firstOffset.1 ≤ 6 ∧
        -6 ≤ firstOffset.2 ∧ firstOffset.2 ≤ 6)
    (secondBounds :
      -6 ≤ secondOffset.1 ∧ secondOffset.1 ≤ 6 ∧
        -6 ≤ secondOffset.2 ∧ secondOffset.2 ≤ 6)
    (equal :
      Cell.add
          (Cell.scale
            PeriodicEightOccurrenceSplitPositioned.refinementScale firstBase)
          firstOffset =
        Cell.add
          (Cell.scale
            PeriodicEightOccurrenceSplitPositioned.refinementScale secondBase)
          secondOffset) :
    firstBase = secondBase ∧ firstOffset = secondOffset := by
  rcases firstBase with ⟨firstX, firstY⟩
  rcases secondBase with ⟨secondX, secondY⟩
  rcases firstOffset with ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffset with ⟨secondOffsetX, secondOffsetY⟩
  simp only [Cell.add, Cell.scale,
    PeriodicEightOccurrenceSplitPositioned.refinementScale,
    Prod.mk.injEq] at equal ⊢
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- A translated equality between two positioned split variables identifies
their translated source macrocells and their local ring offsets. -/
private theorem finalSourceOccurrencePosition_eq_translated_macrocell
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (first second : ThreeOccurrenceVariable Variable)
    (relativeTranslate : Cell)
    (positionsEqual :
      (PeriodicEightOccurrenceSplitPositioned.placement
          sourcePlacement).position first =
        Cell.add
          ((PeriodicEightOccurrenceSplitPositioned.placement
              sourcePlacement).translation relativeTranslate)
          ((PeriodicEightOccurrenceSplitPositioned.placement
              sourcePlacement).position second)) :
    sourcePlacement.position first.1 =
        Cell.add (sourcePlacement.translation relativeTranslate)
          (sourcePlacement.position second.1) ∧
      finalSourceOccurrenceOffset sourcePlacement first =
        finalSourceOccurrenceOffset sourcePlacement second := by
  rcases finalSourceOccurrenceOffset_data sourcePlacement first with
    ⟨firstBounds, firstPositionEq⟩
  rcases finalSourceOccurrenceOffset_data sourcePlacement second with
    ⟨secondBounds, secondPositionEq⟩
  let translatedSecondBase :=
    Cell.add (sourcePlacement.translation relativeTranslate)
      (sourcePlacement.position second.1)
  have macrocellEqual :
      Cell.add
          (Cell.scale
            PeriodicEightOccurrenceSplitPositioned.refinementScale
            (sourcePlacement.position first.1))
          (finalSourceOccurrenceOffset sourcePlacement first) =
        Cell.add
          (Cell.scale
            PeriodicEightOccurrenceSplitPositioned.refinementScale
            translatedSecondBase)
          (finalSourceOccurrenceOffset sourcePlacement second) := by
    calc
      _ = (PeriodicEightOccurrenceSplitPositioned.placement
            sourcePlacement).position first := firstPositionEq.symm
      _ = Cell.add
            ((PeriodicEightOccurrenceSplitPositioned.placement
                sourcePlacement).translation relativeTranslate)
            ((PeriodicEightOccurrenceSplitPositioned.placement
                sourcePlacement).position second) := positionsEqual
      _ = _ := by
        rw [secondPositionEq]
        apply Prod.ext <;>
          simp [translatedSecondBase,
            PeriodicEightOccurrenceSplitPositioned.placement,
            PeriodicEightOccurrenceSplitPositioned.refinementScale,
            PeriodicVariablePlacement.translation,
            Cell.add, Cell.scale] <;>
          ring
  have separated :=
    finalSourceTightMacrocell_eq
      (sourcePlacement.position first.1) translatedSecondBase
      (finalSourceOccurrenceOffset sourcePlacement first)
      (finalSourceOccurrenceOffset sourcePlacement second)
      firstBounds secondBounds macrocellEqual
  exact ⟨by simpa [translatedSecondBase] using separated.1, separated.2⟩

/-- Clockwise literal ordering and the outer clearance scaling preserve
membership in the underlying logical fixed-eight split. -/
private theorem clearance_variableOccurrence_mem_splitFormula
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {occurrence :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)}
    (occurrenceMember :
      occurrence ∈
        (retainedFigureNineClearancePositionedFormula
          source).erase.variableOccurrences) :
    occurrence ∈
      (retainedDrawingEightOccurrenceSplitFormula
        source).variableOccurrences := by
  have orderedMember :
      occurrence ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).erase.variableOccurrences := by
    simpa only [retainedFigureNineClearancePositionedFormula,
      PositionedPeriodicCNF.erase_scale] using occurrenceMember
  have occurrencePermutation :=
    PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
  have refinedMember :
      occurrence ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).erase.variableOccurrences :=
    occurrencePermutation.mem_iff.mp
      (by
        simpa only [
          retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula]
          using orderedMember)
  simpa only [
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
    using refinedMember

/-- Stored clearance-clause positions identify their presentation indices
even modulo a whole clearance period.  Subtracting each clause anchor turns
the asserted stored-position equality into the existing canonical-position
separation statement. -/
theorem retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstClause.position =
        Cell.add
          ((retainedFigureNineClearancePlacement source).translation
            relativeTranslate)
          secondClause.position) :
    firstClauseIndex = secondClauseIndex := by
  rcases exists_clockwiseClause_of_clearanceClause_mem firstMember with
    ⟨firstSourceClause, firstSourceMember, firstClauseEqual⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem secondMember with
    ⟨secondSourceClause, secondSourceMember, secondClauseEqual⟩
  subst firstClause
  subst secondClause
  let placement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  have unscaledPositionsEqual :
      firstSourceClause.position =
        Cell.add (placement.translation relativeTranslate)
          secondSourceClause.position := by
    apply Cell.scale_injective
      (show (retainedFigureNineSourceClearanceFactor : Int) ≠ 0 by
        simp [retainedFigureNineSourceClearanceFactor])
    simpa [placement, retainedFigureNineClearancePlacement,
      Cell.scale_add] using positionsEqual
  let adjustedTranslate :=
    Cell.add
      (Cell.sub relativeTranslate
        (PeriodicCNF.clauseAnchor firstSourceClause.literals))
      (PeriodicCNF.clauseAnchor secondSourceClause.literals)
  have canonicalPositionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstSourceClause =
        Cell.add (placement.translation adjustedTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondSourceClause) := by
    rcases firstPositionEq : firstSourceClause.position with
      ⟨firstX, firstY⟩
    rcases secondPositionEq : secondSourceClause.position with
      ⟨secondX, secondY⟩
    rcases firstAnchorEq :
        PeriodicCNF.clauseAnchor firstSourceClause.literals with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases secondAnchorEq :
        PeriodicCNF.clauseAnchor secondSourceClause.literals with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp only [PositionedPeriodicCNF.canonicalClausePosition,
      adjustedTranslate, PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale, firstPositionEq,
      secondPositionEq, firstAnchorEq, secondAnchorEq,
      Prod.mk.injEq] at unscaledPositionsEqual ⊢
    constructor <;> nlinarith
  exact
    retainedOrderedFixedEightCanonicalClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstSourceMember secondSourceMember
      adjustedTranslate canonicalPositionsEqual

/-- Consequently two genuine clearance clauses in the same stored-position
orbit are the same positioned clause as well as the same list entry. -/
theorem retainedFigureNineClearanceClausePosition_eq_translated_imp_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstClause.position =
        Cell.add
          ((retainedFigureNineClearancePlacement source).translation
            relativeTranslate)
          secondClause.position) :
    firstClause = secondClause := by
  have indicesEqual :=
    retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstMember secondMember
      relativeTranslate positionsEqual
  subst secondClauseIndex
  have firstLookup := (List.mem_zipIdx_iff_getElem?).mp firstMember
  have secondLookup := (List.mem_zipIdx_iff_getElem?).mp secondMember
  rw [firstLookup] at secondLookup
  exact Option.some.inj (by simpa using secondLookup)

/-- Genuine fixed-eight variables in the clearance source occupy distinct
orbits modulo the whole clearance period.  The factor-36 ring macrocell first
recovers the underlying retained source-variable orbit; the retained gauge
then rules out a nonzero period shift, and the local ring code recovers the
exact occurrence copy. -/
theorem retainedFigureNineClearanceVariablePosition_eq_translated_imp_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {first second :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable)}
    (firstMember :
      first ∈
        (retainedFigureNineClearancePositionedFormula
          source).erase.variableOccurrences)
    (secondMember :
      second ∈
        (retainedFigureNineClearancePositionedFormula
          source).erase.variableOccurrences)
    (relativeTranslate : Cell)
    (positionsEqual :
      (retainedFigureNineClearancePlacement source).position first =
        Cell.add
          ((retainedFigureNineClearancePlacement source).translation
            relativeTranslate)
          ((retainedFigureNineClearancePlacement source).position second)) :
    first = second := by
  let basePlacement :=
    (finalCoordinatedPlacement source).scale
      retainedAngularFanSourceClearanceFactor
  let splitPlacement :=
    PeriodicEightOccurrenceSplitPositioned.placement basePlacement
  have refinedPositionsEqual :
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).position first =
        Cell.add
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              source).translation relativeTranslate)
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              source).position second) := by
    apply Cell.scale_injective
      (show (retainedFigureNineSourceClearanceFactor : Int) ≠ 0 by
        simp [retainedFigureNineSourceClearanceFactor])
    simpa [retainedFigureNineClearancePlacement,
      Cell.scale_add] using positionsEqual
  have splitPositionsEqual :
      splitPlacement.position first =
        Cell.add (splitPlacement.translation relativeTranslate)
          (splitPlacement.position second) := by
    apply Cell.scale_injective
      (show (retainedTerminalFanRoutingRefinement : Int) ≠ 0 by
        simp [retainedTerminalFanRoutingRefinement])
    simpa [splitPlacement, basePlacement,
      retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
      retainedAngularFanSourceScaledRefinedPlacement,
      retainedAngularFanRefinedPlacement,
      finalCoordinatedPlacement, Cell.scale_add] using
        refinedPositionsEqual
  have firstSplitMember :=
    clearance_variableOccurrence_mem_splitFormula source firstMember
  have secondSplitMember :=
    clearance_variableOccurrence_mem_splitFormula source secondMember
  have firstLogicalMember :
      first ∈
        (PeriodicEightOccurrenceSplit.formula
          (retainedPlanarSATFormula source)
          (retainedDrawingAngularOccurrencePorts source)).variableOccurrences := by
    simpa [retainedDrawingEightOccurrenceSplitFormula] using firstSplitMember
  have secondLogicalMember :
      second ∈
        (PeriodicEightOccurrenceSplit.formula
          (retainedPlanarSATFormula source)
          (retainedDrawingAngularOccurrencePorts source)).variableOccurrences := by
    simpa [retainedDrawingEightOccurrenceSplitFormula] using secondSplitMember
  have firstCopyMember :
      first ∈ PeriodicEightOccurrenceSplit.copies first.1 :=
    formula_variableOccurrence_mem_copies
      (retainedPlanarSATFormula source)
      (retainedDrawingAngularOccurrencePorts source)
      firstLogicalMember
  have secondCopyMember :
      second ∈ PeriodicEightOccurrenceSplit.copies second.1 :=
    formula_variableOccurrence_mem_copies
      (retainedPlanarSATFormula source)
      (retainedDrawingAngularOccurrencePorts source)
      secondLogicalMember
  have firstSourceVariable :
      first.1 ∈ sourceVariables (retainedPlanarSATFormula source) :=
    PeriodicEightOccurrenceSplit.formula_variableOccurrences_fst_mem_sourceVariables
      (retainedPlanarSATFormula source)
      (retainedDrawingAngularOccurrencePorts source)
      firstLogicalMember
  have secondSourceVariable :
      second.1 ∈ sourceVariables (retainedPlanarSATFormula source) :=
    PeriodicEightOccurrenceSplit.formula_variableOccurrences_fst_mem_sourceVariables
      (retainedPlanarSATFormula source)
      (retainedDrawingAngularOccurrencePorts source)
      secondLogicalMember
  have firstScaledSourceVariable :
      first.1 ∈ sourceVariables
        (((finalCoordinatedSource source).scale
          retainedAngularFanSourceClearanceFactor).erase) := by
    simpa [finalCoordinatedSource, retainedPlanarSATFormula] using
      firstSourceVariable
  have secondScaledSourceVariable :
      second.1 ∈ sourceVariables
        (((finalCoordinatedSource source).scale
          retainedAngularFanSourceClearanceFactor).erase) := by
    simpa [finalCoordinatedSource, retainedPlanarSATFormula] using
      secondSourceVariable
  have macrocellEqual :=
    finalSourceOccurrencePosition_eq_translated_macrocell
      basePlacement first second relativeTranslate splitPositionsEqual
  have sourceAtomsEqual : first.1 = second.1 := by
    by_cases translateZero : relativeTranslate = (0, 0)
    · subst relativeTranslate
      apply
        retainedFinalCoordinatedScaledPlacement_position_injective_on_sourceVariables
          source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
          firstScaledSourceVariable secondScaledSourceVariable
      simpa [basePlacement, PeriodicVariablePlacement.translation,
        Cell.add, Cell.scale] using macrocellEqual.1
    · exfalso
      exact
        (retainedFinalCoordinatedScaledPlacement_position_ne_add_translation_of_nonzero
          source first.1 second.1 relativeTranslate translateZero)
          (by
            simpa [basePlacement, Cell.add, add_comm] using macrocellEqual.1)
  have ringPositionsEqual :
      OccurrenceSplitRing.ringVariablePosition
          (PeriodicEightOccurrenceSplit.ringVertexOfIndex first.2.1) =
        OccurrenceSplitRing.ringVariablePosition
          (PeriodicEightOccurrenceSplit.ringVertexOfIndex second.2.1) := by
    apply cellSub_right_injective (12, 12)
    simpa [finalSourceOccurrenceOffset] using macrocellEqual.2
  have ringVerticesEqual :
      PeriodicEightOccurrenceSplit.ringVertexOfIndex first.2.1 =
        PeriodicEightOccurrenceSplit.ringVertexOfIndex second.2.1 :=
    ringVariablePosition_injective ringPositionsEqual
  calc
    first =
        PeriodicEightOccurrenceSplit.ringCopy first.1
          (PeriodicEightOccurrenceSplit.ringVertexOfIndex first.2.1) :=
      (ringCopy_ringVertexOfIndex_eq_of_mem_copies
        first.1 firstCopyMember).symm
    _ = PeriodicEightOccurrenceSplit.ringCopy second.1
          (PeriodicEightOccurrenceSplit.ringVertexOfIndex second.2.1) := by
      rw [sourceAtomsEqual, ringVerticesEqual]
    _ = second :=
      ringCopy_ringVertexOfIndex_eq_of_mem_copies
        second.1 secondCopyMember

end PeriodicOrthocrossing
end LeanTrominoes
