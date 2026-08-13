/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineMixedRouteSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRouteSeparation

/-!
# Complete retained Figure 9 route separation

The inherited, auxiliary, and mixed pair theorems are combined here into
the unconditional relative route-separation certificate for the retained
ordered Figure 9 construction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

local instance orderedCompleteRouteVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem generatedOccurrenceCoordinatesDifferent_of_flatDifferent
    {Variable : Type*} [DecidableEq Variable]
    (formula : PositionedPeriodicCNF Variable)
    {first second : CNFIncidence Variable × Nat}
    (firstMember :
      first ∈
        (PeriodicCNF.incidencesWithMetadata formula.erase).zipIdx)
    (secondMember :
      second ∈
        (PeriodicCNF.incidencesWithMetadata formula.erase).zipIdx)
    (relativeTranslate : Cell)
    (flatOccurrencesDifferent :
      (first.2, (0, 0)) ≠
        (second.2, relativeTranslate)) :
    ((first.1.clauseIndex, first.1.literalIndex), (0, 0)) ≠
      ((second.1.clauseIndex, second.1.literalIndex),
        relativeTranslate) := by
  intro coordinateOccurrencesEqual
  have clauseIndexEqual :
      first.1.clauseIndex = second.1.clauseIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
      coordinateOccurrencesEqual
  have literalIndexEqual :
      first.1.literalIndex = second.1.literalIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
      coordinateOccurrencesEqual
  have relativeTranslateZero : (0, 0) = relativeTranslate :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
      coordinateOccurrencesEqual
  have flatIndexEqual : first.2 = second.2 := by
    by_contra flatIndicesDifferent
    rcases
        PositionedPeriodicCNF.incidenceCoordinatesDistinct_of_flatIndicesDistinct
          formula firstMember secondMember flatIndicesDifferent with
      clauseIndicesDifferent | literalIndicesDifferent
    · exact clauseIndicesDifferent clauseIndexEqual
    · exact literalIndicesDifferent literalIndexEqual
  apply flatOccurrencesDifferent
  exact Prod.ext flatIndexEqual relativeTranslateZero

private theorem inherited_or_not_inherited
    {Variable : Type*}
    (atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :
    (∃ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        atom = .inl (.inl sourceAtom)) ∨
      (∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        atom ≠ .inl (.inl sourceAtom)) := by
  rcases atom with inheritedOrFigureNine | unitAuxiliary
  · rcases inheritedOrFigureNine with sourceAtom | figureNineAuxiliary
    · exact Or.inl ⟨sourceAtom, rfl⟩
    · exact Or.inr (by
        intro sourceAtom equal
        cases equal)
  · exact Or.inr (by
      intro sourceAtom equal
      cases equal)

/-- Two inherited incidences have separated complete retained routes. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_both_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate))
    (firstSourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (firstInherited :
      firstLiteral.atom = .inl (.inl firstSourceAtom))
    (secondSourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (secondInherited :
      secondLiteral.atom = .inl (.inl secondSourceAtom)) :
    RoutesAvoidEachOther
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseIndex firstLiteralIndex)
      ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
            source).translation relativeTranslate))) := by
  rcases
      retainedOrderedFixedEightCompleteRouteSuffixes_eq_fanInheritedRouteSuffix_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
        firstSourceAtom firstInherited with
    ⟨firstData, firstLookup, _firstSuffixShape⟩
  rcases
      retainedOrderedFixedEightCompleteRouteSuffixes_eq_fanInheritedRouteSuffix_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        secondSourceAtom secondInherited with
    ⟨secondData, secondLookup, _secondSuffixShape⟩
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let original :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have avoidances :=
    retainedOrderedFixedEightFigureNine_relativeSplicedRoutePairAvoidances_of_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstData secondData
      firstLookup secondLookup relativeTranslate
      generatedOccurrencesDifferent
  have components :=
    PlanarOneInThreeNoUnitsFigureNine.relativeSplicedRoutePairComponentsSeparated_of_avoidances
      clearanceSource clearancePlacement clearanceWidth
      clearanceDistinct original
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember relativeTranslate
      avoidances
  simpa [
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    clearanceSource, clearancePlacement, clearanceWidth,
    clearanceDistinct, original] using
    PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_relative_avoidEachOther_of_components
      clearanceSource clearancePlacement clearanceWidth
      clearanceDistinct original
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember relativeTranslate
      components

/-- All distinct relative pairs of complete retained Figure 9 routes are
separated, across inherited, auxiliary, and mixed pairs. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  intro first firstMember second secondMember
    relativeTranslate flatOccurrencesDifferent
  let formula :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      formula firstMember with
    ⟨firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember, _firstIncidenceEqual⟩
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      formula secondMember with
    ⟨secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember, _secondIncidenceEqual⟩
  have generatedOccurrencesDifferent :
      ((first.1.clauseIndex, first.1.literalIndex), (0, 0)) ≠
        ((second.1.clauseIndex, second.1.literalIndex),
          relativeTranslate) :=
    generatedOccurrenceCoordinatesDifferent_of_flatDifferent
      formula firstMember secondMember relativeTranslate
      flatOccurrencesDifferent
  rcases inherited_or_not_inherited firstLiteral.atom with
    ⟨firstSourceAtom, firstInherited⟩ | firstNotInherited
  · rcases inherited_or_not_inherited secondLiteral.atom with
      ⟨secondSourceAtom, secondInherited⟩ | secondNotInherited
    · exact
        retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_both_inherited
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember relativeTranslate
          generatedOccurrencesDifferent
          firstSourceAtom firstInherited
          secondSourceAtom secondInherited
    · exact
        retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_first_inherited_second_not_inherited
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember relativeTranslate
          generatedOccurrencesDifferent
          firstSourceAtom firstInherited secondNotInherited
  · rcases inherited_or_not_inherited secondLiteral.atom with
      ⟨secondSourceAtom, secondInherited⟩ | secondNotInherited
    · exact
        retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_first_not_inherited_second_inherited
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember relativeTranslate
          generatedOccurrencesDifferent firstNotInherited
          secondSourceAtom secondInherited
    · exact
        retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_both_not_inherited
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstClauseMember secondClauseMember
          firstLiteralMember secondLiteralMember relativeTranslate
          generatedOccurrencesDifferent
          firstNotInherited secondNotInherited

/-- The normalized retained ordered Figure 9 drawing is ribbon-ready. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady := by
  exact
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_rawRelativeIncidenceRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)

end PeriodicOrthocrossing
end LeanTrominoes
