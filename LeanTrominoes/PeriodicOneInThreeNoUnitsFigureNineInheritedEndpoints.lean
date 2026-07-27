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
