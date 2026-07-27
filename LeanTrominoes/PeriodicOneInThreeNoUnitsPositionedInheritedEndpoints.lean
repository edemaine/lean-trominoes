import LeanTrominoes.PeriodicOneInThreeNoUnitsInheritedIncidences
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedNormalizedLocalRoutes

/-!
# Unit-elimination endpoints inherited from source incidences

An inherited unit-elimination literal ends at an index-selected boundary
port of its source-clause box.  This file expresses that port in the
generated clause's canonical anchor gauge and recovers its exact source
literal occurrence through the flattened positioned formula.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- The displayed source-clause vertex expressed in a generated
unit-elimination clause's canonical anchor gauge after refinement. -/
def normalizedSourceClausePosition
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)) :
    Cell :=
  Cell.sub
    (Cell.scale gadgetScale sourceClause.position)
    (outputPlacement.translation
      (PeriodicCNF.clauseAnchor generatedClause.literals))

/-- The unit-elimination boundary port for one source occurrence, in the
generated clause's canonical anchor gauge. -/
def normalizedSourcePort
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceLiteralIndex : Nat) :
    Cell :=
  Cell.add
    (normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause)
    (PlanarOneInThreeNoUnits.sourceLocalPosition sourceLiteralIndex)

/-- Every inherited unit-elimination incidence recovers a genuine source
literal occurrence and ends at its index-selected normalized boundary port. -/
theorem normalizedLocalEndpoint_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
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
            (placement source sourcePlacement)
            metadata.sourceClause clause sourceLiteralIndex := by
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have generatedClauseMember :
      metadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          metadata.sourceClauseIndex
          metadata.sourceClause.literals := by
    rw [← clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨metadata.clause,
        List.fst_mem_of_mem_zipIdx localClauseMember,
        rfl⟩
  have generatedLiteralMember :
      literal ∈ metadata.clause.literals :=
    List.fst_mem_of_mem_zipIdx metadataLiteralMember
  rcases
      PeriodicOneInThreeNoUnits.inherited_of_mem_clauseClauses
        metadata.sourceClauseIndex
        metadata.sourceClause.literals
        generatedClauseMember generatedLiteralMember
        sourceAtom literalSource with
    ⟨sourceLiteral, sourceLiteralIndex,
      sourceLiteralMember, sourceLiteralAtom, literalOffset⟩
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
      sourceLiteralMember, sourceLiteralAtom, literalOffset, ?_⟩
  subst clause
  simp only [normalizedLocalEndpoint, metadataLookup]
  rw [(List.mem_zipIdx_iff_getElem?).mp metadataLiteralMember]
  simp only
  rw [literalSource, ← sourceLiteralAtom,
    PlanarOneInThreeNoUnits.instantiatedDrawing_sourcePosition
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth metadataDistinct sourceLiteralMember]
  apply Prod.ext <;>
  simp [normalizedSourcePort, normalizedSourceClausePosition,
    Cell.add, Cell.sub]
  <;> ring

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
