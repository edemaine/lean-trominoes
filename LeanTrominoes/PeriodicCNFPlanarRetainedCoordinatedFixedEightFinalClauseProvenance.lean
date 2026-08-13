/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrbits

/-!
# Provenance of final composed Figure Nine clauses

The macrocell address of a final clause records its local Figure Nine clause
and its unit-elimination role.  This file additionally retains the exact
metadata lookups connecting those local indices to the two flattened global
clause enumerations.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Exact source and flattening provenance for one final composed clause. -/
inductive FinalFigureNineClauseSource
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable)) →
      Nat → Cell → FinalFigureNineLocalAddress → Prop
  | generated
      (sourceClause : PositionedPeriodicClause Variable)
      (sourceClauseIndex : Nat)
      (sourceClauseMember :
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx)
      (figureNineClauseStart localFinalClauseIndex : Nat)
      (finalClause :
        PositionedPeriodicClause
          (OneInThreeNoUnitVariable (OneInThreeVariable Variable)))
      (finalClauseIndex : Nat)
      (composedMetadataLookup :
        (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source)[
            finalClauseIndex]? =
          some
            ({ sourceClause := sourceClause
               sourceClauseIndex := sourceClauseIndex
               figureNineClauseStart := figureNineClauseStart
               clause := finalClause
               localClauseIndex := localFinalClauseIndex } :
              PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata Variable))
      (figureNineClause :
        PositionedPeriodicClause (OneInThreeVariable Variable))
      (figureNineClauseIndex : Nat)
      (localFigureNineClauseIndex : Fin 6)
      (localFigureNineClauseMember :
        (figureNineClause, localFigureNineClauseIndex.val) ∈
          (PeriodicOneInThreePositioned.clauseGadget
            sourceClauseIndex sourceClause).zipIdx)
      (figureNineMetadataLookup :
        (PeriodicOneInThreePositioned.formulaClauseMetadata source)[
            figureNineClauseIndex]? =
          some
            ({ sourceClause := sourceClause
               sourceClauseIndex := sourceClauseIndex
               clause := figureNineClause
               localClauseIndex := localFigureNineClauseIndex.val } :
              PeriodicOneInThreePositioned.ClauseMetadata Variable))
      (unitClauseIndex : Nat)
      (unitClauseMember :
        (finalClause, unitClauseIndex) ∈
          (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
            figureNineClauseIndex figureNineClause).zipIdx)
      (unitMetadataLookup :
        (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
          figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            sourceClauseIndex sourceClause))[localFinalClauseIndex]? =
          some
            ({ sourceClause := figureNineClause
               sourceClauseIndex := figureNineClauseIndex
               clause := finalClause
               localClauseIndex := unitClauseIndex } :
              PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata
                (OneInThreeVariable Variable))) :
      FinalFigureNineClauseSource source finalClause finalClauseIndex
        sourceClause.position
        (.finalClause localFigureNineClauseIndex
          (finalUnitClauseLocal figureNineClause.literals unitClauseIndex))

/-- Every final clause has exact two-stage flattening provenance together
with its `72 × 72` macrocell orbit. -/
theorem composedFinalClause_inMacrocellOrbit_withSource
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePeriod : Nat)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx) :
    ∃ base address,
      FinalFigureNineClauseSource source clause clauseIndex base address ∧
      Cell.InMacrocellOrbit finalFigureNineMacrocellScale sourcePeriod
        base address.position clause.position := by
  rcases PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      sourceClauseMember, _localClauseMember⟩
  have metadataIndexLt :
      clauseIndex <
        (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
          source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source)[
          clauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  rcases
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_unitEliminationMetadata_lookup_valid
        source metadataMember with
    ⟨unitMetadata, unitMetadataLookup, unitClauseEqual,
      unitSourceClauseMember, unitClauseMember⟩
  rw [List.zipIdx_eq_map_add] at unitSourceClauseMember
  rcases List.mem_map.mp unitSourceClauseMember with
    ⟨taggedFigureNineClause, localFigureNineClauseMember,
      taggedFigureNineClauseEqual⟩
  have figureNineClauseEqual :
      taggedFigureNineClause.1 = unitMetadata.sourceClause :=
    congrArg Prod.fst taggedFigureNineClauseEqual
  have figureNineClauseIndexEqual :
      metadata.figureNineClauseStart + taggedFigureNineClause.2 =
        unitMetadata.sourceClauseIndex :=
    congrArg Prod.snd taggedFigureNineClauseEqual
  have localFigureNineClauseIndexLt : taggedFigureNineClause.2 < 6 :=
    lt_of_lt_of_le
      (List.mem_zipIdx' localFigureNineClauseMember).1
      (PeriodicOneInThreePositioned.clauseGadget_length_le_six
        metadata.sourceClauseIndex metadata.sourceClause)
  let localFigureNineClauseIndex : Fin 6 :=
    ⟨taggedFigureNineClause.2, localFigureNineClauseIndexLt⟩
  have figureNineMetadataLookup :=
    PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_figureNineMetadata_lookup
      source metadataMember localFigureNineClauseMember
  have exactComposedMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source)[
          clauseIndex]? =
        some
          ({ sourceClause := metadata.sourceClause
             sourceClauseIndex := metadata.sourceClauseIndex
             figureNineClauseStart := metadata.figureNineClauseStart
             clause := clause
             localClauseIndex := metadata.localClauseIndex } :
            PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata Variable) := by
    rw [← metadataClauseEqual]
    convert metadataLookup using 1
  have exactFigureNineMetadataLookup :
      (PeriodicOneInThreePositioned.formulaClauseMetadata source)[
          unitMetadata.sourceClauseIndex]? =
        some
          ({ sourceClause := metadata.sourceClause
             sourceClauseIndex := metadata.sourceClauseIndex
             clause := unitMetadata.sourceClause
             localClauseIndex := localFigureNineClauseIndex.val } :
            PeriodicOneInThreePositioned.ClauseMetadata Variable) := by
    simpa [localFigureNineClauseIndex, figureNineClauseEqual,
      figureNineClauseIndexEqual] using figureNineMetadataLookup
  have exactUnitMetadataLookup :
      (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
        metadata.figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex metadata.sourceClause))[
            metadata.localClauseIndex]? =
        some
          ({ sourceClause := unitMetadata.sourceClause
             sourceClauseIndex := unitMetadata.sourceClauseIndex
             clause := clause
             localClauseIndex := unitMetadata.localClauseIndex } :
            PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata
              (OneInThreeVariable Variable)) := by
    rw [← metadataClauseEqual, ← unitClauseEqual]
    convert unitMetadataLookup using 1
  have exactUnitClauseMember :
      (clause, unitMetadata.localClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
          unitMetadata.sourceClauseIndex
          unitMetadata.sourceClause).zipIdx := by
    simpa [unitClauseEqual, metadataClauseEqual] using unitClauseMember
  have figureNinePosition :
      unitMetadata.sourceClause.position =
        PlanarOneInThree.generatedClausePosition
          metadata.sourceClause.position localFigureNineClauseIndex.val := by
    rw [← figureNineClauseEqual]
    exact
      PeriodicOneInThreePositioned.clauseGadget_position_eq_generatedClausePosition
        metadata.sourceClauseIndex metadata.sourceClause
        localFigureNineClauseMember
  have firstOrbit :
      Cell.InMacrocellOrbit 12 sourcePeriod metadata.sourceClause.position
        (PeriodicOneInThreePositioned.generatedClauseLocalPosition
          localFigureNineClauseIndex.val)
        unitMetadata.sourceClause.position := by
    rw [figureNinePosition]
    exact
      PeriodicOneInThreePositioned.generatedClausePosition_inMacrocellOrbit
        sourcePeriod metadata.sourceClause.position
        localFigureNineClauseIndex.val
  have unitPosition :
      clause.position =
        PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition
          unitMetadata.sourceClause unitMetadata.localClauseIndex := by
    rw [← metadataClauseEqual, ← unitClauseEqual]
    exact
      PeriodicOneInThreeNoUnitsPositioned.clauseGadget_position_eq_generatedClausePosition
        unitMetadata.sourceClauseIndex unitMetadata.sourceClause
        unitClauseMember
  have secondOrbit :
      Cell.InMacrocellOrbit 6 (12 * sourcePeriod)
        unitMetadata.sourceClause.position
        (PeriodicOneInThreeNoUnitsPositioned.generatedClauseLocalPosition
          unitMetadata.sourceClause.literals unitMetadata.localClauseIndex)
        clause.position := by
    rw [unitPosition]
    exact
      PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition_inMacrocellOrbit
        (12 * sourcePeriod) unitMetadata.sourceClause
        unitMetadata.localClauseIndex
  have orbit := firstOrbit.compose secondOrbit
  let address : FinalFigureNineLocalAddress :=
    .finalClause localFigureNineClauseIndex
      (finalUnitClauseLocal unitMetadata.sourceClause.literals
        unitMetadata.localClauseIndex)
  refine ⟨metadata.sourceClause.position, address, ?_, ?_⟩
  · exact FinalFigureNineClauseSource.generated
      metadata.sourceClause metadata.sourceClauseIndex sourceClauseMember
      metadata.figureNineClauseStart metadata.localClauseIndex
      clause clauseIndex exactComposedMetadataLookup
      unitMetadata.sourceClause unitMetadata.sourceClauseIndex
      localFigureNineClauseIndex
      (by
        have taggedExact :
            taggedFigureNineClause =
              (unitMetadata.sourceClause,
                localFigureNineClauseIndex.val) := by
          apply Prod.ext
          · exact figureNineClauseEqual
          · rfl
        rw [← taggedExact]
        exact localFigureNineClauseMember)
      exactFigureNineMetadataLookup unitMetadata.localClauseIndex
      exactUnitClauseMember exactUnitMetadataLookup
  · simpa [address, finalFigureNineMacrocellScale,
      FinalFigureNineLocalAddress.position,
      finalFigureNineClauseLocalPosition,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PeriodicOneInThreePositioned.generatedClauseLocalPosition,
      finalUnitClauseLocal_position] using orbit

/-- Specialization of exact clause provenance to the retained fixed-eight
source used by the hardness construction. -/
theorem retainedOrderedFixedEightComposedRawClause_inMacrocellOrbit_withSource
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx) :
    ∃ base address,
      FinalFigureNineClauseSource
          (retainedFigureNineClearancePositionedFormula source)
          clause clauseIndex base address ∧
        Cell.InMacrocellOrbit finalFigureNineMacrocellScale
          (retainedFigureNineClearancePlacement source).period
          base address.position clause.position := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula]
    using
      composedFinalClause_inMacrocellOrbit_withSource
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source).period clauseMember

end PeriodicOrthocrossing
end LeanTrominoes
