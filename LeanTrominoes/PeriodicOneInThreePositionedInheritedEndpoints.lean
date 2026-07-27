import LeanTrominoes.PeriodicOneInThreeInheritedIncidences
import LeanTrominoes.PeriodicOneInThreePositionedNormalizedLocalRoutes

/-!
# Figure 9 endpoints inherited from source incidences

An inherited Figure 9 literal ends at a boundary port of its source-clause
box.  The whole box must be expressed in the generated clause's logical
anchor gauge: different Figure 9 rows can begin at different source-literal
offsets.  This file identifies that exact point and recovers the source
literal presentation index that selects its port.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- The displayed source-clause vertex expressed in a generated clause's
canonical anchor gauge after Figure 9 refinement. -/
def normalizedSourceClausePosition
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable)) :
    Cell :=
  Cell.sub
    (Cell.scale PlanarOneInThree.gadgetScale sourceClause.position)
    (outputPlacement.translation
      (PeriodicCNF.clauseAnchor generatedClause.literals))

/-- The Figure 9 boundary port for one source occurrence, in the generated
clause's canonical anchor gauge. -/
def normalizedSourcePort
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeVariable Variable))
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeVariable Variable))
    (sourceLiteralIndex : Nat) :
    Cell :=
  Cell.add
    (normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause)
    (PlanarOneInThreePositioned.sourceLocalPosition sourceLiteralIndex)

/-- Every inherited Figure 9 incidence recovers a genuine source literal
occurrence, and its normalized local route ends at that occurrence's
index-selected source-clause boundary port. -/
theorem normalizedLocalEndpoint_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal :
      PeriodicLiteral (OneInThreeVariable Variable)}
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
        PeriodicOneInThree.clauseClauses
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
      PeriodicOneInThree.inherited_of_mem_clauseClauses
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
    PlanarOneInThreePositioned.instantiatedDrawing_sourcePosition
      metadata.sourceClauseIndex metadata.sourceClause
      metadataWidth metadataDistinct sourceLiteralMember]
  apply Prod.ext <;>
  simp [normalizedSourcePort, normalizedSourceClausePosition,
    Cell.add, Cell.sub]
  <;> ring

end PeriodicOneInThreePositioned
end LeanTrominoes
