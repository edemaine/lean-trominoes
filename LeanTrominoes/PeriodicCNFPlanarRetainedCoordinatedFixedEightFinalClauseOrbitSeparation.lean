import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseProvenance
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalSourceOrbitSeparation
import LeanTrominoes.PeriodicOneInThreePositionedKeyInjectivity
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedKeyFromInjectivity

/-!
# Orbit separation of final composed Figure Nine clauses

Finite local addresses identify the Figure Nine clause and unit-elimination
role inside a source macrocell.  Exact metadata provenance then converts
those local identities back into both flattened presentation indices.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxRecDepth 10000

/-- On genuine clauses of one unit-elimination gadget, the finite local role
identifies the exact generated-clause index. -/
private theorem finalUnitClauseLocal_eq_imp_index_eq
    {Variable : Type*}
    (figureNineClauseIndex : Nat)
    (figureNineClause : PositionedPeriodicClause Variable)
    {firstClause secondClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
          figureNineClauseIndex figureNineClause).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
          figureNineClauseIndex figureNineClause).zipIdx)
    (rolesEqual :
      finalUnitClauseLocal figureNineClause.literals firstIndex =
        finalUnitClauseLocal figureNineClause.literals secondIndex) :
    firstIndex = secondIndex := by
  have firstLt := (List.mem_zipIdx' firstMember).1
  have secondLt := (List.mem_zipIdx' secondMember).1
  cases figureNineClause with
  | mk position literals =>
      cases literals with
      | nil =>
          simp [PeriodicOneInThreeNoUnitsPositioned.clauseGadget,
            PeriodicOneInThreeNoUnits.clauseClauses] at firstLt secondLt
          interval_cases firstIndex <;> interval_cases secondIndex <;>
            simp [finalUnitClauseLocal] at rolesEqual ⊢
      | cons first rest =>
          cases rest with
          | nil =>
              simp [PeriodicOneInThreeNoUnitsPositioned.clauseGadget,
                PeriodicOneInThreeNoUnits.clauseClauses] at firstLt secondLt
              interval_cases firstIndex <;> interval_cases secondIndex <;>
                simp [finalUnitClauseLocal] at rolesEqual ⊢
          | cons second tail =>
              simp [PeriodicOneInThreeNoUnitsPositioned.clauseGadget,
                PeriodicOneInThreeNoUnits.clauseClauses] at firstLt secondLt
              omega

/-- Raw translated equality of two final clause positions yields equal
source macrocells and equal finite addresses. -/
private theorem retainedComposedRawClausePosition_eq_translated_data
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstClause.position =
        Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).translation relativeTranslate)
          secondClause.position) :
    ∃ firstBase secondBase firstAddress secondAddress baseTranslate,
      FinalFigureNineClauseSource
          (retainedFigureNineClearancePositionedFormula source)
          firstClause firstClauseIndex firstBase firstAddress ∧
        FinalFigureNineClauseSource
          (retainedFigureNineClearancePositionedFormula source)
          secondClause secondClauseIndex secondBase secondAddress ∧
        firstBase =
          Cell.add
            ((retainedFigureNineClearancePlacement source).translation
              baseTranslate)
            secondBase ∧
        firstAddress = secondAddress := by
  rcases
      retainedOrderedFixedEightComposedRawClause_inMacrocellOrbit_withSource
        source firstMember with
    ⟨firstBase, firstAddress, firstSource, firstOrbit⟩
  rcases
      retainedOrderedFixedEightComposedRawClause_inMacrocellOrbit_withSource
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
      firstClause.position =
        Cell.add
          (Cell.scale
            (finalFigureNineMacrocellScale *
              (retainedFigureNineClearancePlacement source).period)
            relativeTranslate)
          secondClause.position := by
    rw [PeriodicVariablePlacement.translation, rawPeriod] at positionsEqual
    exact positionsEqual
  rcases Cell.inMacrocellOrbit_eq_periodTranslate
      (show 0 < finalFigureNineMacrocellScale by native_decide)
      (finalFigureNineLocalAddress_position_halfOpen firstAddress)
      (finalFigureNineLocalAddress_position_halfOpen secondAddress)
      firstOrbit secondOrbit refinedPositionsEqual with
    ⟨baseTranslate, basesEqual, localPositionsEqual⟩
  have addressesEqual : firstAddress = secondAddress :=
    finalFigureNineLocalAddress_position_injective localPositionsEqual
  refine ⟨firstBase, secondBase, firstAddress, secondAddress,
    baseTranslate, firstSource, secondSource, ?_, addressesEqual⟩
  simpa [PeriodicVariablePlacement.translation] using basesEqual

/-- Stored raw final-clause positions identify their presentation indices
even modulo the whole final period. -/
theorem retainedOrderedFixedEightComposedRawClausePosition_eq_translated_imp_clauseIndex_eq
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
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstClause.position =
        Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).translation relativeTranslate)
          secondClause.position) :
    firstClauseIndex = secondClauseIndex := by
  rcases retainedComposedRawClausePosition_eq_translated_data
      source firstMember secondMember relativeTranslate positionsEqual with
    ⟨_firstBase, _secondBase, _firstAddress, _secondAddress, baseTranslate,
      firstSource, secondSource, basesEqual, addressesEqual⟩
  cases firstSource with
  | generated firstSourceClause firstSourceClauseIndex firstSourceClauseMember
      firstFigureNineClauseStart firstLocalFinalClauseIndex _ _
      firstComposedMetadataLookup firstFigureNineClause
      firstFigureNineClauseIndex firstLocalFigureNineClauseIndex
      firstLocalFigureNineClauseMember firstFigureNineMetadataLookup
      firstUnitClauseIndex firstUnitClauseMember firstUnitMetadataLookup =>
    cases secondSource with
    | generated secondSourceClause secondSourceClauseIndex
        secondSourceClauseMember secondFigureNineClauseStart
        secondLocalFinalClauseIndex _ _ secondComposedMetadataLookup
        secondFigureNineClause secondFigureNineClauseIndex
        secondLocalFigureNineClauseIndex secondLocalFigureNineClauseMember
        secondFigureNineMetadataLookup secondUnitClauseIndex
        secondUnitClauseMember secondUnitMetadataLookup =>
      have localFigureNineIndicesEqual :
          firstLocalFigureNineClauseIndex =
            secondLocalFigureNineClauseIndex := by
        injection addressesEqual
      have unitRolesEqual :
          finalUnitClauseLocal firstFigureNineClause.literals
              firstUnitClauseIndex =
            finalUnitClauseLocal secondFigureNineClause.literals
              secondUnitClauseIndex := by
        injection addressesEqual
      have sourceClauseIndicesEqual :=
        retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstSourceClauseMember
          secondSourceClauseMember baseTranslate basesEqual
      have sourceClausesEqual :=
        retainedFigureNineClearanceClausePosition_eq_translated_imp_eq
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstSourceClauseMember
          secondSourceClauseMember baseTranslate basesEqual
      have firstComposedMetadataMember :
          ({ sourceClause := firstSourceClause
             sourceClauseIndex := firstSourceClauseIndex
             figureNineClauseStart := firstFigureNineClauseStart
             clause := firstClause
             localClauseIndex := firstLocalFinalClauseIndex } :
            PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
              (ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable))) ∈
          PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
            (retainedFigureNineClearancePositionedFormula source) :=
        List.mem_iff_getElem?.mpr
          ⟨firstClauseIndex, firstComposedMetadataLookup⟩
      have secondComposedMetadataMember :
          ({ sourceClause := secondSourceClause
             sourceClauseIndex := secondSourceClauseIndex
             figureNineClauseStart := secondFigureNineClauseStart
             clause := secondClause
             localClauseIndex := secondLocalFinalClauseIndex } :
            PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
              (ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable))) ∈
          PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
            (retainedFigureNineClearancePositionedFormula source) :=
        List.mem_iff_getElem?.mpr
          ⟨secondClauseIndex, secondComposedMetadataLookup⟩
      have figureNineStartsEqual :
          firstFigureNineClauseStart = secondFigureNineClauseStart :=
        (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_sourceBlock_eq
          (retainedFigureNineClearancePositionedFormula source)
          firstComposedMetadataMember secondComposedMetadataMember
          sourceClauseIndicesEqual).2
      have figureNineClauseIndicesEqual :
          firstFigureNineClauseIndex = secondFigureNineClauseIndex := by
        apply
          PeriodicOneInThreePositioned.formulaClauseMetadata_lookup_key_injective
            (retainedFigureNineClearancePositionedFormula source)
            firstFigureNineMetadataLookup secondFigureNineMetadataLookup
        simp [PeriodicOneInThreePositioned.ClauseMetadata.key,
          sourceClauseIndicesEqual, localFigureNineIndicesEqual]
      subst secondFigureNineClauseIndex
      rw [firstFigureNineMetadataLookup] at secondFigureNineMetadataLookup
      have figureNineMetadataEqual :
          ({ sourceClause := firstSourceClause
             sourceClauseIndex := firstSourceClauseIndex
             clause := firstFigureNineClause
             localClauseIndex := firstLocalFigureNineClauseIndex.val } :
            PeriodicOneInThreePositioned.ClauseMetadata
              (ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable))) =
          ({ sourceClause := secondSourceClause
             sourceClauseIndex := secondSourceClauseIndex
             clause := secondFigureNineClause
             localClauseIndex := secondLocalFigureNineClauseIndex.val } :
            PeriodicOneInThreePositioned.ClauseMetadata
              (ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable))) :=
        Option.some.inj secondFigureNineMetadataLookup
      have figureNineClausesEqual :
          firstFigureNineClause = secondFigureNineClause := by
        exact congrArg PeriodicOneInThreePositioned.ClauseMetadata.clause
          figureNineMetadataEqual
      subst secondFigureNineClause
      have unitClauseIndicesEqual :
          firstUnitClauseIndex = secondUnitClauseIndex := by
        apply finalUnitClauseLocal_eq_imp_index_eq
          firstFigureNineClauseIndex firstFigureNineClause
          firstUnitClauseMember secondUnitClauseMember
        simpa using unitRolesEqual
      have localFinalClauseIndicesEqual :
          firstLocalFinalClauseIndex = secondLocalFinalClauseIndex := by
        subst secondFigureNineClauseStart
        subst secondSourceClauseIndex
        subst secondSourceClause
        apply
          PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom_lookup_key_injective
            firstFigureNineClauseStart
            (PeriodicOneInThreePositioned.clauseGadget
              firstSourceClauseIndex firstSourceClause)
            firstUnitMetadataLookup secondUnitMetadataLookup
        simp [PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata.key,
          unitClauseIndicesEqual]
      apply
        PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_key_injective
          (retainedFigureNineClearancePositionedFormula source)
          firstComposedMetadataLookup secondComposedMetadataLookup
      simp [PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata.key,
        sourceClauseIndicesEqual, localFinalClauseIndicesEqual]

/-- Consequently, two genuine raw final clauses in the same stored-position
orbit are the same positioned clause as well as the same list entry. -/
theorem retainedOrderedFixedEightComposedRawClausePosition_eq_translated_imp_eq
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
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstClause.position =
        Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).translation relativeTranslate)
          secondClause.position) :
    firstClause = secondClause := by
  have indicesEqual :=
    retainedOrderedFixedEightComposedRawClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      firstMember secondMember relativeTranslate positionsEqual
  subst secondClauseIndex
  have firstLookup := (List.mem_zipIdx_iff_getElem?).mp firstMember
  have secondLookup := (List.mem_zipIdx_iff_getElem?).mp secondMember
  rw [firstLookup] at secondLookup
  exact Option.some.inj (by simpa using secondLookup)

end PeriodicOrthocrossing
end LeanTrominoes
