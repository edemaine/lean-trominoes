import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalSourceOrbitSeparation
import LeanTrominoes.PeriodicOneInThreePositionedKeyInjectivity

/-!
# Orbit separation of final composed Figure Nine variables

The final local-code classification reduces every collision modulo the
refined period to an equality of source macrocells and an equality in the
finite `72 × 72` address table.  Source orbit separation then identifies the
underlying source variable or clause, while metadata-key injectivity recovers
the global scope of second-stage auxiliary variables.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxRecDepth 10000

/-- Equality modulo the raw final period recovers equal source macrocells and
equal finite local addresses. -/
private theorem retainedComposedRawVariablePosition_eq_translated_data
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {first second :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (firstMember :
      first ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences)
    (secondMember :
      second ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences)
    (relativeTranslate : Cell)
    (positionsEqual :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).position first =
        Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).translation relativeTranslate)
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).position second)) :
    ∃ firstBase secondBase firstAddress secondAddress baseTranslate,
      FinalFigureNineVariableSource
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          first firstBase firstAddress ∧
        FinalFigureNineVariableSource
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          second secondBase secondAddress ∧
        firstBase =
          Cell.add
            ((retainedFigureNineClearancePlacement source).translation
              baseTranslate)
            secondBase ∧
        firstAddress = secondAddress := by
  rcases
      retainedOrderedFixedEightComposedRawVariableOccurrence_inMacrocellOrbit
        source firstMember with
    ⟨firstBase, firstAddress, firstSource, firstOrbit⟩
  rcases
      retainedOrderedFixedEightComposedRawVariableOccurrence_inMacrocellOrbit
        source secondMember with
    ⟨secondBase, secondAddress, secondSource, secondOrbit⟩
  have rawPeriod :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).period =
        finalFigureNineMacrocellScale *
          (retainedFigureNineClearancePlacement source).period := by
    simp [
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreePositioned.placement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      finalFigureNineMacrocellScale,
      PlanarOneInThree.gadgetScale,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale]
    omega
  have refinedPositionsEqual :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).position first =
        Cell.add
          (Cell.scale
            (finalFigureNineMacrocellScale *
              (retainedFigureNineClearancePlacement source).period)
            relativeTranslate)
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).position second) := by
    rw [PeriodicVariablePlacement.translation, rawPeriod] at positionsEqual
    exact positionsEqual
  rcases Cell.inMacrocellOrbit_eq_periodTranslate
      (show 0 < finalFigureNineMacrocellScale by
        native_decide)
      (finalFigureNineLocalAddress_position_halfOpen firstAddress)
      (finalFigureNineLocalAddress_position_halfOpen secondAddress)
      firstOrbit secondOrbit refinedPositionsEqual with
    ⟨baseTranslate, basesEqual, localPositionsEqual⟩
  have addressesEqual : firstAddress = secondAddress :=
    finalFigureNineLocalAddress_position_injective localPositionsEqual
  refine ⟨firstBase, secondBase, firstAddress, secondAddress,
    baseTranslate, firstSource, secondSource, ?_, addressesEqual⟩
  simpa [PeriodicVariablePlacement.translation] using basesEqual

/-- The raw composed placement is injective on genuine final variable
occurrences modulo its whole physical period. -/
theorem retainedOrderedFixedEightComposedRawVariablePosition_eq_translated_imp_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {first second :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (firstMember :
      first ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences)
    (secondMember :
      second ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences)
    (relativeTranslate : Cell)
    (positionsEqual :
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).position first =
        Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).translation relativeTranslate)
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).position second)) :
    first = second := by
  rcases retainedComposedRawVariablePosition_eq_translated_data
      source firstMember secondMember relativeTranslate positionsEqual with
    ⟨firstBase, secondBase, firstAddress, secondAddress, baseTranslate,
      firstSource, secondSource, basesEqual, addressesEqual⟩
  cases firstSource with
  | inherited firstAtom firstAtomMember =>
      cases secondSource with
      | inherited secondAtom secondAtomMember =>
          have atomsEqual :=
            retainedFigureNineClearanceVariablePosition_eq_translated_imp_eq
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty firstAtomMember secondAtomMember
              baseTranslate basesEqual
          subst secondAtom
          rfl
      | figureNineAuxiliary => simp at addressesEqual
      | unitEliminationAuxiliary => simp at addressesEqual
  | figureNineAuxiliary firstClause firstClauseIndex firstClauseMember
      firstKind =>
      cases secondSource with
      | inherited => simp at addressesEqual
      | figureNineAuxiliary secondClause secondClauseIndex secondClauseMember
          secondKind =>
          have kindsEqual : firstKind = secondKind := by
            injection addressesEqual
          have clauseIndicesEqual :=
            retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty firstClauseMember secondClauseMember
              baseTranslate basesEqual
          have clausesEqual :=
            retainedFigureNineClearanceClausePosition_eq_translated_imp_eq
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty firstClauseMember secondClauseMember
              baseTranslate basesEqual
          subst secondKind
          subst secondClauseIndex
          subst secondClause
          rfl
      | unitEliminationAuxiliary => simp at addressesEqual
  | unitEliminationAuxiliary firstClause firstClauseIndex firstClauseMember
      firstFigureNineClause firstFigureNineClauseIndex
      firstLocalFigureNineClauseIndex firstLocalFigureNineClauseMember
      firstFigureNineClauseMember firstFigureNineMetadataLookup firstKind =>
      cases secondSource with
      | inherited => simp at addressesEqual
      | figureNineAuxiliary => simp at addressesEqual
      | unitEliminationAuxiliary secondClause secondClauseIndex
          secondClauseMember secondFigureNineClause
          secondFigureNineClauseIndex secondLocalFigureNineClauseIndex
          secondLocalFigureNineClauseMember secondFigureNineClauseMember
          secondFigureNineMetadataLookup secondKind =>
          have localIndicesEqual :
              firstLocalFigureNineClauseIndex =
                secondLocalFigureNineClauseIndex := by
            injection addressesEqual
          have kindsEqual : firstKind = secondKind := by
            injection addressesEqual
          have sourceClauseIndicesEqual :=
            retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty firstClauseMember secondClauseMember
              baseTranslate basesEqual
          have sourceClausesEqual :=
            retainedFigureNineClearanceClausePosition_eq_translated_imp_eq
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty firstClauseMember secondClauseMember
              baseTranslate basesEqual
          have figureNineClauseIndicesEqual :
              firstFigureNineClauseIndex =
                secondFigureNineClauseIndex := by
            apply
              PeriodicOneInThreePositioned.formulaClauseMetadata_lookup_key_injective
                (retainedFigureNineClearancePositionedFormula source)
                firstFigureNineMetadataLookup
                secondFigureNineMetadataLookup
            simp [PeriodicOneInThreePositioned.ClauseMetadata.key,
              sourceClauseIndicesEqual, localIndicesEqual]
          subst secondFigureNineClauseIndex
          rw [firstFigureNineMetadataLookup] at secondFigureNineMetadataLookup
          have metadataEqual :
              ({ sourceClause := firstClause
                 sourceClauseIndex := firstClauseIndex
                 clause := firstFigureNineClause
                 localClauseIndex :=
                   firstLocalFigureNineClauseIndex.val } :
                PeriodicOneInThreePositioned.ClauseMetadata
                  (ThreeOccurrenceVariable
                    (WrappedPeriodicPlanarSATVariable Variable))) =
              ({ sourceClause := secondClause
                 sourceClauseIndex := secondClauseIndex
                 clause := secondFigureNineClause
                 localClauseIndex :=
                   secondLocalFigureNineClauseIndex.val } :
                PeriodicOneInThreePositioned.ClauseMetadata
                  (ThreeOccurrenceVariable
                    (WrappedPeriodicPlanarSATVariable Variable))) :=
            Option.some.inj secondFigureNineMetadataLookup
          have figureNineClausesEqual :
              firstFigureNineClause = secondFigureNineClause :=
            congrArg PeriodicOneInThreePositioned.ClauseMetadata.clause
              metadataEqual
          subst secondFigureNineClause
          subst secondKind
          rfl

end PeriodicOrthocrossing
end LeanTrominoes
