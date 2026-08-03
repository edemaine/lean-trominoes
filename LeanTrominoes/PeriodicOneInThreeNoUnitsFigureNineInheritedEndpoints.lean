import LeanTrominoes.PeriodicOneInThreeInheritedIncidences
import LeanTrominoes.PeriodicOneInThreeNoUnitsInheritedIncidences
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes

/-!
# Composed endpoints inherited from original source incidences

A twice-inherited literal in the final unit-free exact-one formula comes
from one precise occurrence in the original source clause.  This file
classifies that occurrence through both local transformations at once and
identifies the endpoint of its certified composed route with the appropriate
boundary port of the original source clause's `72 × 72` refinement box.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

/-- The displayed original source-clause vertex expressed in a final
clause's canonical anchor gauge after both refinements. -/
def normalizedSourceClausePosition
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))) :
    Cell :=
  Cell.sub
    (Cell.scale composedGadgetScale sourceClause.position)
    (outputPlacement.translation
      (PeriodicCNF.clauseAnchor generatedClause.literals))

/-- The composed boundary port for an original source occurrence, in the
final generated clause's canonical anchor gauge. -/
def normalizedSourcePort
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)))
    (sourceLiteralIndex : Nat) :
    Cell :=
  Cell.add
    (normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause)
    (sourceLocalPosition sourceLiteralIndex)

/-- The complete provenance and endpoint certificate for one final
incidence inherited through both unit elimination and Figure 9. -/
structure InheritedEndpointProvenance
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clauseIndex literalIndex : Nat) where
  generatedClause :
    PositionedPeriodicClause
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
  generatedLiteral :
    PeriodicLiteral
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
  sourceClause : PositionedPeriodicClause Variable
  sourceClauseIndex : Nat
  sourceLiteral : PeriodicLiteral Variable
  sourceLiteralIndex : Nat
  metadata : ClauseMetadata Variable
  metadataLookup :
    (formulaClauseMetadata source)[clauseIndex]? = some metadata
  metadataClause : metadata.clause = generatedClause
  metadataSourceClause : metadata.sourceClause = sourceClause
  metadataSourceClauseIndex :
    metadata.sourceClauseIndex = sourceClauseIndex
  unitMetadata :
    PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata
      (OneInThreeVariable Variable)
  unitMetadataLookup :
    (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
      metadata.figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget
        metadata.sourceClauseIndex metadata.sourceClause))[
          metadata.localClauseIndex]? =
      some unitMetadata
  unitMetadataClause : unitMetadata.clause = generatedClause
  figureNineLiteral : PeriodicLiteral (OneInThreeVariable Variable)
  figureNineLiteralIndex : Nat
  generatedClauseMember :
    (generatedClause, clauseIndex) ∈
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx
  generatedLiteralMember :
    (generatedLiteral, literalIndex) ∈
      generatedClause.literals.zipIdx
  sourceClauseMember :
    (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx
  sourceLiteralMember :
    (sourceLiteral, sourceLiteralIndex) ∈
      sourceClause.literals.zipIdx
  figureNineLiteralMember :
    (figureNineLiteral, figureNineLiteralIndex) ∈
      unitMetadata.sourceClause.literals.zipIdx
  generatedLiteralAtom :
    generatedLiteral.atom = .inl figureNineLiteral.atom
  figureNineLiteralAtom :
    figureNineLiteral.atom = .inl sourceLiteral.atom
  literalAtom :
    generatedLiteral.atom = .inl (.inl sourceLiteral.atom)
  literalOffset : generatedLiteral.offset = sourceLiteral.offset
  localEndpoint :
    normalizedLocalEndpoint source sourcePlacement
        clauseIndex literalIndex =
      normalizedSourcePort
        (composedPlacement source sourcePlacement)
        sourceClause generatedClause sourceLiteralIndex
  unitOriginalOccurrencePair :
    ((generatedLiteral, clauseIndex, literalIndex),
      (figureNineLiteral, unitMetadata.sourceClauseIndex,
        figureNineLiteralIndex)) ∈
      PeriodicOneInThreeNoUnits.formulaOriginalOccurrencePairs
        (PeriodicOneInThreePositioned.formula source).erase
        figureNineLiteral.atom
  figureNineOriginalOccurrencePair :
    ((figureNineLiteral, unitMetadata.sourceClauseIndex,
        figureNineLiteralIndex),
      (sourceLiteral, sourceClauseIndex, sourceLiteralIndex)) ∈
      PeriodicOneInThree.formulaOriginalOccurrencePairs
        source.erase sourceLiteral.atom

/-- Every twice-inherited final incidence has a canonical two-layer
occurrence provenance certificate together with its composed endpoint. -/
theorem inheritedEndpointProvenance_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl (.inl sourceAtom)) :
    Nonempty
      (InheritedEndpointProvenance
        source sourcePlacement clauseIndex literalIndex) := by
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, metadataClause,
      sourceClauseMember, _localClauseMember⟩
  have metadataIndexLt :
      clauseIndex < (formulaClauseMetadata source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataMember : metadata ∈ formulaClauseMetadata source := by
    rw [← (List.getElem?_eq_some_iff.mp metadataLookup).2]
    exact List.getElem_mem metadataIndexLt
  rcases formulaClauseMetadata_unitEliminationMetadata_lookup_valid
      source metadataMember with
    ⟨unitMetadata, unitMetadataLookup, unitMetadataClause,
      unitSourceClauseMember, unitGeneratedClauseMember⟩
  have unitGeneratedLiteralMember :
      (literal, literalIndex) ∈
        unitMetadata.clause.literals.zipIdx := by
    simpa [unitMetadataClause, metadataClause] using literalMember
  have finalClauseLiteralsMember :
      unitMetadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          unitMetadata.sourceClauseIndex
          unitMetadata.sourceClause.literals := by
    rw [← PeriodicOneInThreeNoUnitsPositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨unitMetadata.clause,
        List.fst_mem_of_mem_zipIdx unitGeneratedClauseMember, rfl⟩
  have finalLiteralMember : literal ∈ unitMetadata.clause.literals :=
    List.fst_mem_of_mem_zipIdx unitGeneratedLiteralMember
  rcases
      PeriodicOneInThreeNoUnits.inherited_of_mem_clauseClauses
        unitMetadata.sourceClauseIndex
        unitMetadata.sourceClause.literals
        finalClauseLiteralsMember finalLiteralMember
        (.inl sourceAtom) literalSource with
    ⟨figureNineLiteral, figureNineLiteralIndex,
      figureNineLiteralMember, figureNineLiteralAtom,
      finalLiteralOffset⟩
  rw [List.zipIdx_eq_map_add] at unitSourceClauseMember
  rcases List.mem_map.mp unitSourceClauseMember with
    ⟨taggedFigureNineClause, figureNineClauseMember,
      taggedFigureNineClauseEqual⟩
  have figureNineClauseEqual :
      taggedFigureNineClause.1 = unitMetadata.sourceClause :=
    congrArg Prod.fst taggedFigureNineClauseEqual
  have figureNineClauseIndexEqual :
      metadata.figureNineClauseStart + taggedFigureNineClause.2 =
        unitMetadata.sourceClauseIndex :=
    congrArg Prod.snd taggedFigureNineClauseEqual
  have exactFigureNineMetadataLookup :=
    formulaClauseMetadata_figureNineMetadata_lookup
      source metadataMember figureNineClauseMember
  have figureNineClauseLiteralsMember :
      unitMetadata.sourceClause.literals ∈
        PeriodicOneInThree.clauseClauses
          metadata.sourceClauseIndex metadata.sourceClause.literals := by
    rw [← PeriodicOneInThreePositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨unitMetadata.sourceClause, by
        simpa [figureNineClauseEqual] using
          List.fst_mem_of_mem_zipIdx figureNineClauseMember,
        rfl⟩
  have figureNineLiteralMem :
      figureNineLiteral ∈ unitMetadata.sourceClause.literals :=
    List.fst_mem_of_mem_zipIdx figureNineLiteralMember
  rcases
      PeriodicOneInThree.inherited_of_mem_clauseClauses
        metadata.sourceClauseIndex metadata.sourceClause.literals
        figureNineClauseLiteralsMember figureNineLiteralMem
        sourceAtom figureNineLiteralAtom with
    ⟨sourceLiteral, sourceLiteralIndex,
      sourceLiteralMember, sourceLiteralAtom,
      figureNineLiteralOffset⟩
  have sourceClauseMem : metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth : metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, sourceClauseMem, rfl⟩
  have metadataDistinct : metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause sourceClauseMem
  have generatedLiteralAtom :
      literal.atom = .inl figureNineLiteral.atom := by
    rw [literalSource, figureNineLiteralAtom]
  have figureNineLiteralSourceAtom :
      figureNineLiteral.atom = .inl sourceLiteral.atom := by
    rw [figureNineLiteralAtom, sourceLiteralAtom]
  have literalAtom :
      literal.atom = .inl (.inl sourceLiteral.atom) := by
    rw [literalSource, sourceLiteralAtom]
  have localEndpoint :
      normalizedLocalEndpoint source sourcePlacement
          clauseIndex literalIndex =
        normalizedSourcePort
          (composedPlacement source sourcePlacement)
          metadata.sourceClause clause sourceLiteralIndex := by
    subst clause
    simp only [normalizedLocalEndpoint, metadataLookup]
    rw [(List.mem_zipIdx_iff_getElem?).mp literalMember]
    simp only
    rw [literalSource, ← sourceLiteralAtom,
      instantiatedDrawing_sourcePosition
        metadata.sourceClauseIndex
        metadata.figureNineClauseStart
        metadata.sourceClause metadataWidth metadataDistinct
        sourceLiteralMember]
    apply Prod.ext <;>
    simp [normalizedSourcePort, normalizedSourceClausePosition,
      Cell.add, Cell.sub]
    <;> ring
  have globalUnitMetadataLookup :=
    formulaClauseMetadata_unitEliminationMetadata_global_lookup
      source metadataLookup unitMetadataLookup
  have figureNineFormulaWidth :
      (PeriodicOneInThreePositioned.formula source).erase.WidthAtMost 3 := by
    rw [PeriodicOneInThreePositioned.erase_formula]
    exact PeriodicOneInThree.formula_widthAtMostThree source.erase
  have figureNineFormulaDistinct :
      (PeriodicOneInThreePositioned.formula source).AllAtomsNodup :=
    PeriodicOneInThreePositioned.formula_allAtomsNodup source
  have unitOriginalOccurrencePair :=
    PeriodicOneInThreeNoUnitsPositioned.originalOccurrencePair_of_formulaMetadataLookup
      (PeriodicOneInThreePositioned.formula source)
      figureNineFormulaWidth figureNineFormulaDistinct
      figureNineLiteral.atom globalUnitMetadataLookup
      unitGeneratedLiteralMember
      figureNineLiteralMember generatedLiteralAtom rfl
  have figureNineOriginalOccurrencePair :=
    PeriodicOneInThreePositioned.originalOccurrencePair_of_formulaMetadataLookup
      source sourceWidth sourceDistinct sourceLiteral.atom
      exactFigureNineMetadataLookup
      (by simpa [figureNineClauseEqual] using figureNineLiteralMember)
      sourceLiteralMember figureNineLiteralSourceAtom rfl
  refine ⟨{
    generatedClause := clause
    generatedLiteral := literal
    sourceClause := metadata.sourceClause
    sourceClauseIndex := metadata.sourceClauseIndex
    sourceLiteral := sourceLiteral
    sourceLiteralIndex := sourceLiteralIndex
    metadata := metadata
    metadataLookup := metadataLookup
    metadataClause := metadataClause
    metadataSourceClause := rfl
    metadataSourceClauseIndex := rfl
    unitMetadata := unitMetadata
    unitMetadataLookup := unitMetadataLookup
    unitMetadataClause := unitMetadataClause.trans metadataClause
    figureNineLiteral := figureNineLiteral
    figureNineLiteralIndex := figureNineLiteralIndex
    generatedClauseMember := clauseMember
    generatedLiteralMember := literalMember
    sourceClauseMember := sourceClauseMember
    sourceLiteralMember := sourceLiteralMember
    figureNineLiteralMember := figureNineLiteralMember
    generatedLiteralAtom := generatedLiteralAtom
    figureNineLiteralAtom := by
      exact figureNineLiteralSourceAtom
    literalAtom := literalAtom
    literalOffset := finalLiteralOffset.trans figureNineLiteralOffset
    localEndpoint := localEndpoint
    unitOriginalOccurrencePair := by
      simpa [figureNineClauseIndexEqual] using unitOriginalOccurrencePair
    figureNineOriginalOccurrencePair := by
      simpa [figureNineClauseIndexEqual] using
        figureNineOriginalOccurrencePair }⟩

/-- Every twice-inherited final incidence recovers a genuine occurrence in
the original source clause, preserves its periodic offset, and ends at its
index-selected composed boundary port. -/
theorem normalizedLocalEndpoint_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource :
      literal.atom = .inl (.inl sourceAtom)) :
    ∃ metadata sourceLiteral sourceLiteralIndex,
      (formulaClauseMetadata source)[clauseIndex]? =
          some metadata ∧
        metadata.clause = clause ∧
        (metadata.sourceClause, metadata.sourceClauseIndex) ∈
          source.clauses.zipIdx ∧
        (sourceLiteral, sourceLiteralIndex) ∈
          metadata.sourceClause.literals.zipIdx ∧
        sourceLiteral.atom = sourceAtom ∧
        literal.offset = sourceLiteral.offset ∧
        normalizedLocalEndpoint source sourcePlacement
            clauseIndex literalIndex =
          normalizedSourcePort
            (composedPlacement source sourcePlacement)
            metadata.sourceClause clause sourceLiteralIndex := by
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have finalClauseMember :
      metadata.clause ∈
        unitEliminationClausesFrom
          metadata.figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex
            metadata.sourceClause) :=
    List.fst_mem_of_mem_zipIdx localClauseMember
  rw [unitEliminationClausesFrom_eq_localZipIdx]
    at finalClauseMember
  rcases List.mem_flatMap.mp finalClauseMember with
    ⟨taggedFigureNineClause, taggedFigureNineClauseMember,
      finalClauseInGadget⟩
  have finalClauseLiteralsMember :
      metadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          (metadata.figureNineClauseStart +
            taggedFigureNineClause.2)
          taggedFigureNineClause.1.literals := by
    rw [←
      PeriodicOneInThreeNoUnitsPositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨metadata.clause, finalClauseInGadget, rfl⟩
  have finalLiteralMember :
      literal ∈ metadata.clause.literals :=
    List.fst_mem_of_mem_zipIdx metadataLiteralMember
  rcases
      PeriodicOneInThreeNoUnits.inherited_of_mem_clauseClauses
        (metadata.figureNineClauseStart +
          taggedFigureNineClause.2)
        taggedFigureNineClause.1.literals
        finalClauseLiteralsMember finalLiteralMember
        (.inl sourceAtom) literalSource with
    ⟨figureNineLiteral, figureNineLiteralIndex,
      figureNineLiteralMember, figureNineLiteralAtom,
      finalLiteralOffset⟩
  have figureNineClauseMember :
      taggedFigureNineClause.1.literals ∈
        PeriodicOneInThree.clauseClauses
          metadata.sourceClauseIndex
          metadata.sourceClause.literals := by
    rw [← PeriodicOneInThreePositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨taggedFigureNineClause.1,
        List.fst_mem_of_mem_zipIdx
          taggedFigureNineClauseMember,
        rfl⟩
  have figureNineLiteralMem :
      figureNineLiteral ∈
        taggedFigureNineClause.1.literals :=
    List.fst_mem_of_mem_zipIdx figureNineLiteralMember
  rcases
      PeriodicOneInThree.inherited_of_mem_clauseClauses
        metadata.sourceClauseIndex
        metadata.sourceClause.literals
        figureNineClauseMember figureNineLiteralMem
        sourceAtom figureNineLiteralAtom with
    ⟨sourceLiteral, sourceLiteralIndex,
      sourceLiteralMember, sourceLiteralAtom,
      figureNineLiteralOffset⟩
  have sourceClauseMem :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, sourceClauseMem, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause sourceClauseMem
  refine
    ⟨metadata, sourceLiteral, sourceLiteralIndex,
      metadataLookup, clauseEqual, sourceClauseMember,
      sourceLiteralMember, sourceLiteralAtom,
      finalLiteralOffset.trans figureNineLiteralOffset, ?_⟩
  subst clause
  simp only [normalizedLocalEndpoint, metadataLookup]
  rw [(List.mem_zipIdx_iff_getElem?).mp metadataLiteralMember]
  simp only
  rw [literalSource, ← sourceLiteralAtom,
    instantiatedDrawing_sourcePosition
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
      sourceLiteralMember]
  apply Prod.ext <;>
  simp [normalizedSourcePort, normalizedSourceClausePosition,
    Cell.add, Cell.sub]
  <;> ring

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
