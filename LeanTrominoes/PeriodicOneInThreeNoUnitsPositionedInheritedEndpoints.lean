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

/-- Local generated-clause endpoint of a source-variable route, selected by
the arity of the source clause. -/
def sourceLocalClausePosition (sourceArity : Nat) : Cell :=
  if sourceArity = 1 then (3, 2) else (3, 3)

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

/-- The three unit-elimination source ports have distinct local
coordinates. -/
theorem sourceLocalPosition_injective_below_three
    {firstIndex secondIndex : Nat}
    (firstLt : firstIndex < 3)
    (secondLt : secondIndex < 3)
    (positionsEqual :
      PlanarOneInThreeNoUnits.sourceLocalPosition firstIndex =
        PlanarOneInThreeNoUnits.sourceLocalPosition secondIndex) :
    firstIndex = secondIndex := by
  have firstCases :
      firstIndex = 0 ∨ firstIndex = 1 ∨ firstIndex = 2 := by
    omega
  have secondCases :
      secondIndex = 0 ∨ secondIndex = 1 ∨ secondIndex = 2 := by
    omega
  rcases firstCases with rfl | rfl | rfl <;>
    rcases secondCases with rfl | rfl | rfl <;>
    simp [PlanarOneInThreeNoUnits.sourceLocalPosition] at positionsEqual ⊢

/-- A generated clause's local vertex is different from every genuine
source port in the same unit-elimination block. -/
theorem sourceLocalClausePosition_ne_sourceLocalPosition
    (sourceArity sourceLiteralIndex : Nat)
    (arityPositive : 0 < sourceArity)
    (arityAtMostThree : sourceArity ≤ 3)
    (sourceLiteralIndexLt : sourceLiteralIndex < sourceArity) :
    sourceLocalClausePosition sourceArity ≠
      PlanarOneInThreeNoUnits.sourceLocalPosition sourceLiteralIndex := by
  have arityCases :
      sourceArity = 1 ∨ sourceArity = 2 ∨ sourceArity = 3 := by
    omega
  have indexCases :
      sourceLiteralIndex = 0 ∨ sourceLiteralIndex = 1 ∨
        sourceLiteralIndex = 2 := by
    omega
  rcases arityCases with rfl | rfl | rfl <;>
    rcases indexCases with rfl | rfl | rfl <;>
    simp [sourceLocalClausePosition,
      PlanarOneInThreeNoUnits.sourceLocalPosition] at sourceLiteralIndexLt ⊢

/-- Generated clauses with the same logical anchor use the same normalized
source-clause origin. -/
theorem normalizedSourceClausePosition_eq_of_anchor_eq
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourceClause : PositionedPeriodicClause Variable)
    (firstClause secondClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (anchorsEqual :
      PeriodicCNF.clauseAnchor firstClause.literals =
        PeriodicCNF.clauseAnchor secondClause.literals) :
    normalizedSourceClausePosition
        outputPlacement sourceClause firstClause =
      normalizedSourceClausePosition
        outputPlacement sourceClause secondClause := by
  simp [normalizedSourceClausePosition, anchorsEqual]

/-- Within one source block and one common anchor gauge, normalized source
ports are injectively indexed by the source literal occurrence. -/
theorem normalizedSourcePort_injective_of_anchor_eq
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourceClause : PositionedPeriodicClause Variable)
    (firstClause secondClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    {firstIndex secondIndex : Nat}
    (firstLt : firstIndex < 3)
    (secondLt : secondIndex < 3)
    (anchorsEqual :
      PeriodicCNF.clauseAnchor firstClause.literals =
        PeriodicCNF.clauseAnchor secondClause.literals)
    (portsEqual :
      normalizedSourcePort outputPlacement sourceClause
          firstClause firstIndex =
        normalizedSourcePort outputPlacement sourceClause
          secondClause secondIndex) :
    firstIndex = secondIndex := by
  apply sourceLocalPosition_injective_below_three firstLt secondLt
  have originsEqual :=
    normalizedSourceClausePosition_eq_of_anchor_eq
      outputPlacement sourceClause firstClause secondClause anchorsEqual
  unfold normalizedSourcePort at portsEqual
  rw [originsEqual] at portsEqual
  exact Cell.add_left_injective _ portsEqual

/-- The local generated-clause vertex and a genuine normalized source port
remain distinct after adding their common normalized source origin. -/
theorem normalizedSourceClauseLocalPosition_ne_port
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceLiteralIndex : Nat)
    (arityPositive : 0 < sourceClause.literals.length)
    (arityAtMostThree : sourceClause.literals.length ≤ 3)
    (sourceLiteralIndexLt :
      sourceLiteralIndex < sourceClause.literals.length) :
    Cell.add
        (normalizedSourceClausePosition
          outputPlacement sourceClause generatedClause)
        (sourceLocalClausePosition sourceClause.literals.length) ≠
      normalizedSourcePort outputPlacement sourceClause
        generatedClause sourceLiteralIndex := by
  unfold normalizedSourcePort
  exact fun equal =>
    sourceLocalClausePosition_ne_sourceLocalPosition
      sourceClause.literals.length sourceLiteralIndex
      arityPositive arityAtMostThree sourceLiteralIndexLt
      (Cell.add_left_injective _ equal)

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
