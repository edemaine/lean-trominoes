import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalLocalCodes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineIndex

/-!
# Source macrocells of final Figure Nine clauses

Each clause after Figure Nine and unit elimination retains a unique source
clause block.  This file connects the existing two-stage indexing metadata
to the finite `72 × 72` local-address table.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every clause in a twice-replaced formula lies in the macrocell orbit of
one original source clause at one finite final-clause address. -/
theorem composedFinalClause_inMacrocellOrbit
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
    ∃ sourceClause sourceClauseIndex,
      ∃ address : FinalFigureNineLocalAddress,
      (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx ∧
      Cell.InMacrocellOrbit finalFigureNineMacrocellScale sourcePeriod
        sourceClause.position address.position clause.position := by
  rcases PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataIndexLt :
      clauseIndex <
        (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
          source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        source)[clauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have finalClauseMember :
      metadata.clause ∈
        PlanarOneInThreeNoUnitsFigureNine.unitEliminationClausesFrom
          metadata.figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex metadata.sourceClause) :=
    List.fst_mem_of_mem_zipIdx localClauseMember
  rw [PlanarOneInThreeNoUnitsFigureNine.unitEliminationClausesFrom_eq_localZipIdx]
    at finalClauseMember
  rcases List.mem_flatMap.mp finalClauseMember with
    ⟨taggedFigureNineClause, taggedFigureNineClauseMember,
      finalClauseInGadget⟩
  rcases List.mem_iff_getElem.mp finalClauseInGadget with
    ⟨unitClauseIndex, unitClauseIndexLt, unitClauseAt⟩
  have unitClauseMember :
      (metadata.clause, unitClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
          (metadata.figureNineClauseStart + taggedFigureNineClause.2)
          taggedFigureNineClause.1).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨unitClauseIndexLt, unitClauseAt⟩
  have figureNineClauseIndexLt : taggedFigureNineClause.2 < 6 :=
    lt_of_lt_of_le
      (List.mem_zipIdx' taggedFigureNineClauseMember).1
      (PeriodicOneInThreePositioned.clauseGadget_length_le_six
        metadata.sourceClauseIndex metadata.sourceClause)
  let figureNineClauseIndex : Fin 6 :=
    ⟨taggedFigureNineClause.2, figureNineClauseIndexLt⟩
  let unitClauseKind :=
    finalUnitClauseLocal
      taggedFigureNineClause.1.literals unitClauseIndex
  let address : FinalFigureNineLocalAddress :=
    .finalClause figureNineClauseIndex unitClauseKind
  have figureNinePosition :
      taggedFigureNineClause.1.position =
        PlanarOneInThree.generatedClausePosition
          metadata.sourceClause.position taggedFigureNineClause.2 :=
    PeriodicOneInThreePositioned.clauseGadget_position_eq_generatedClausePosition
      metadata.sourceClauseIndex metadata.sourceClause
      taggedFigureNineClauseMember
  have firstOrbit :
      Cell.InMacrocellOrbit 12 sourcePeriod metadata.sourceClause.position
        (PeriodicOneInThreePositioned.generatedClauseLocalPosition
          taggedFigureNineClause.2)
        taggedFigureNineClause.1.position := by
    rw [figureNinePosition]
    exact
      PeriodicOneInThreePositioned.generatedClausePosition_inMacrocellOrbit
        sourcePeriod metadata.sourceClause.position
        taggedFigureNineClause.2
  have unitPosition :
      metadata.clause.position =
        PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition
          taggedFigureNineClause.1 unitClauseIndex :=
    PeriodicOneInThreeNoUnitsPositioned.clauseGadget_position_eq_generatedClausePosition
      (metadata.figureNineClauseStart + taggedFigureNineClause.2)
      taggedFigureNineClause.1 unitClauseMember
  have secondOrbit :
      Cell.InMacrocellOrbit 6 (12 * sourcePeriod)
        taggedFigureNineClause.1.position
        (PeriodicOneInThreeNoUnitsPositioned.generatedClauseLocalPosition
          taggedFigureNineClause.1.literals unitClauseIndex)
        metadata.clause.position := by
    rw [unitPosition]
    exact
      PeriodicOneInThreeNoUnitsPositioned.generatedClausePosition_inMacrocellOrbit
        (12 * sourcePeriod) taggedFigureNineClause.1 unitClauseIndex
  have composedOrbit := firstOrbit.compose secondOrbit
  refine ⟨metadata.sourceClause, metadata.sourceClauseIndex,
    address, sourceClauseMember, ?_⟩
  rw [← metadataClauseEqual]
  simpa [address, figureNineClauseIndex, unitClauseKind,
    finalFigureNineMacrocellScale,
    FinalFigureNineLocalAddress.position,
    finalFigureNineClauseLocalPosition,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    PeriodicOneInThreePositioned.generatedClauseLocalPosition,
    finalUnitClauseLocal_position] using composedOrbit

/-- Specialization to the actual retained fixed-eight source used by the
hardness construction. -/
theorem retainedOrderedFixedEightComposedRawClause_inMacrocellOrbit
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
    ∃ sourceClause sourceClauseIndex,
      ∃ address : FinalFigureNineLocalAddress,
      (sourceClause, sourceClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula
          source).clauses.zipIdx ∧
      Cell.InMacrocellOrbit finalFigureNineMacrocellScale
        (retainedFigureNineClearancePlacement source).period
        sourceClause.position address.position clause.position := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula]
    using
      composedFinalClause_inMacrocellOrbit
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source).period clauseMember

end PeriodicOrthocrossing
end LeanTrominoes
