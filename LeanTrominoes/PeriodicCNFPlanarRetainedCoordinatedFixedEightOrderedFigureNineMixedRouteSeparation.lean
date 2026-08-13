/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineMixedEndpointSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineAuxiliaryRouteSeparation

/-!
# Relative separation of mixed retained Figure 9 routes

An auxiliary incidence has no global suffix, while an inherited incidence
joins its normalized local route to the retained inherited suffix.  The
local/local separation theorem and strict auxiliary-local/inherited-suffix
separation can therefore be assembled with the one-sided splice lemma.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

local instance orderedMixedRouteVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem generatedOccurrencesDifferent_reverse
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    {relativeTranslate : Cell}
    (different :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    ((secondClauseIndex, secondLiteralIndex), (0, 0)) ≠
      ((firstClauseIndex, firstLiteralIndex),
        Cell.neg relativeTranslate) := by
  intro reverseEqual
  have clauseEqual : secondClauseIndex = firstClauseIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
      reverseEqual
  have literalEqual : secondLiteralIndex = firstLiteralIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
      reverseEqual
  have reverseTranslateZero : (0, 0) = Cell.neg relativeTranslate :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
      reverseEqual
  have relativeTranslateZero : relativeTranslate = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [Cell.neg, Cell.sub] at reverseTranslateZero ⊢
    exact ⟨reverseTranslateZero.1, reverseTranslateZero.2⟩
  apply different
  simp [clauseEqual, literalEqual, relativeTranslateZero]

/-- An auxiliary complete route avoids a relatively translated inherited
complete route. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_first_not_inherited_second_inherited
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
    (firstNotInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        firstLiteral.atom ≠ .inl (.inl sourceAtom))
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
  let suffixes :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      clearanceSource clearancePlacement clearanceWidth
      clearanceDistinct original
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let firstLocal :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement
      firstClauseIndex firstLiteralIndex
  let secondLocal :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement
      secondClauseIndex secondLiteralIndex
  let secondSuffix :=
    suffixes.routes secondClauseIndex secondLiteralIndex
  rcases
      retainedOrderedFixedEightCompleteRouteSuffixes_eq_fanInheritedRouteSuffix_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        secondSourceAtom secondInherited with
    ⟨secondData, _secondDataLookup, secondSuffixShape⟩
  rcases
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
        clearanceSource firstClauseMember with
    ⟨firstMetadata, firstMetadataLookup, _firstMetadataClause,
      _firstSourceClauseMember, _firstEmbeddedClauseMember⟩
  have localsAvoid :
      RoutesAvoidEachOther firstLocal
        (translatePolyline offset secondLocal) := by
    simpa [firstLocal, secondLocal, offset, outputPlacement,
      clearanceSource, clearancePlacement, translatePolyline] using
      retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_avoidEachOther
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember relativeTranslate
        generatedOccurrencesDifferent
  have localStrictlyAvoidsSuffix :
      RoutesStrictlyAvoidEachOther firstLocal
        (translatePolyline offset secondSuffix) := by
    have secondSuffixShape' :
        secondSuffix =
          PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
            outputPlacement clearancePlacement
            secondData.sourceClause secondData.generatedClause
            (PositionedPeriodicCNF.clauseExitFanData
              secondData.sourceClause secondData.sourceClauseIndex
              (retainedFigureNineClearanceIncidenceRoutes source))
            (secondData.sourceSlot clearanceWidth)
            (retainedFigureNineClearanceIncidenceRoutes
              source secondData.sourceClauseIndex
              secondData.sourceLiteralIndex) := by
      simpa [secondSuffix, suffixes, clearanceSource,
        clearancePlacement, clearanceWidth, clearanceDistinct,
        original, outputPlacement] using secondSuffixShape
    rw [secondSuffixShape']
    simpa [firstLocal, secondSuffix, suffixes,
      offset, outputPlacement, clearanceSource, clearancePlacement,
      clearanceWidth, clearanceDistinct, original] using
      retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_not_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
        firstNotInherited firstMetadata firstMetadataLookup
        secondData relativeTranslate
  have secondLocalEndpoints :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      clearanceSource clearancePlacement clearanceWidth clearanceDistinct
      secondClauseMember secondLiteralMember
  have secondSuffixEndpoints :=
    suffixes.endpoints
      secondClause secondClauseIndex secondClauseMember
      secondLiteral secondLiteralIndex secondLiteralMember
  let boundary :=
    Cell.add offset
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
        clearanceSource clearancePlacement
        secondClauseIndex secondLiteralIndex)
  have translatedSecondLocalLast :
      (translatePolyline offset secondLocal).getLast? =
        some boundary := by
    simpa [secondLocal, boundary, translatePolyline] using
      congrArg (Option.map (Cell.add offset)) secondLocalEndpoints.2
  have translatedSecondSuffixHead :
      (translatePolyline offset secondSuffix).head? =
        some boundary := by
    simpa [secondSuffix, boundary, translatePolyline] using
      congrArg (Option.map (Cell.add offset)) secondSuffixEndpoints.1
  have assembled :=
    localsAvoid.join_right_of_strict_suffix
      localStrictlyAvoidsSuffix
      translatedSecondLocalLast translatedSecondSuffixHead
  rw [
    retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
      firstNotInherited]
  change
    RoutesAvoidEachOther firstLocal
      (translatePolyline offset
        (joinAtEndpoint secondLocal secondSuffix))
  rw [translatePolyline_joinAtEndpoint]
  exact assembled

/-- An inherited complete route avoids a relatively translated auxiliary
complete route. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_first_inherited_second_not_inherited
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
    (secondNotInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        secondLiteral.atom ≠ .inl (.inl sourceAtom)) :
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
  let outputPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  let reverseTranslate := Cell.neg relativeTranslate
  let offset := outputPlacement.translation relativeTranslate
  let reverseOffset := outputPlacement.translation reverseTranslate
  have reverseDifferent :
      ((secondClauseIndex, secondLiteralIndex), (0, 0)) ≠
        ((firstClauseIndex, firstLiteralIndex), reverseTranslate) := by
    simpa [reverseTranslate] using
      generatedOccurrencesDifferent_reverse generatedOccurrencesDifferent
  have backwards :=
    retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_first_not_inherited_second_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember firstClauseMember
      secondLiteralMember firstLiteralMember reverseTranslate
      reverseDifferent secondNotInherited firstSourceAtom firstInherited
  have shifted :=
    (routesAvoidEachOther_comm backwards).translate offset
  have shiftCancel : Cell.add reverseOffset offset = (0, 0) := by
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [reverseOffset, offset, outputPlacement, reverseTranslate,
      PeriodicVariablePlacement.translation,
      Cell.neg, Cell.add, Cell.sub, Cell.scale]
  change
    RoutesAvoidEachOther
      (translatePolyline offset
        (translatePolyline reverseOffset
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty firstClauseIndex firstLiteralIndex)))
      (translatePolyline offset
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty secondClauseIndex secondLiteralIndex))
      at shifted
  rw [translatePolyline_add, shiftCancel,
    translatePolyline_zero] at shifted
  simpa [translatePolyline, outputPlacement, offset,
    reverseOffset, reverseTranslate] using shifted

end PeriodicOrthocrossing
end LeanTrominoes
