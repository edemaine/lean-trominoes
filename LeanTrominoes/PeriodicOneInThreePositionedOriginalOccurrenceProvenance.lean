import LeanTrominoes.PeriodicOneInThreeOriginalOccurrenceOrder
import LeanTrominoes.PeriodicOneInThreePositionedIndex
import LeanTrominoes.PlanarOneInThreeLocalDistinctness

/-!
# Figure 9 source-occurrence provenance

The positioned Figure 9 metadata and the logical occurrence-order pairing
traverse the same flattened clause blocks.  This file proves that every
inherited output incidence is paired with the exact source clause and
literal presentation indices recorded by its metadata.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

theorem clauseOriginalOccurrencePairs_mem_of_members
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceClauseIndex : Nat)
    (source : PeriodicClause Variable)
    (sourceWidth : source.length ≤ 3)
    (sourceDistinct :
      (source.map PeriodicLiteral.atom).Nodup)
    {generated : PeriodicClause (OneInThreeVariable Variable)}
    {generatedIndex : Nat}
    (generatedMember :
      (generated, generatedIndex) ∈
        (clauseClauses sourceClauseIndex source).zipIdx)
    {outputLiteral :
      PeriodicLiteral (OneInThreeVariable Variable)}
    {outputLiteralIndex : Nat}
    (outputMember :
      (outputLiteral, outputLiteralIndex) ∈ generated.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceMember :
      (sourceLiteral, sourceLiteralIndex) ∈ source.zipIdx)
    (outputAtom : outputLiteral.atom = .inl atom)
    (sourceAtom : sourceLiteral.atom = atom) :
    ((outputLiteral, outputStart + generatedIndex,
        outputLiteralIndex),
      (sourceLiteral, sourceClauseIndex, sourceLiteralIndex)) ∈
        clauseOriginalOccurrencePairs
          atom outputStart sourceClauseIndex source := by
  rcases source with _ | ⟨first, rest⟩
  · simp at sourceMember
  · rcases rest with _ | ⟨second, rest⟩
    · simp [clauseClauses, disjunctionGadget,
        forcePaddingFalse, auxiliary, padding,
        liftLiteral, negate] at generatedMember
      rcases generatedMember with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all [clauseOriginalOccurrencePairs,
          originalOccurrencePairIf, liftLiteral] <;> aesop
    · rcases rest with _ | ⟨third, rest⟩
      · simp [clauseClauses, disjunctionGadget,
          forcePaddingFalse, auxiliary, padding,
          liftLiteral, negate] at generatedMember
        rcases generatedMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp_all [clauseOriginalOccurrencePairs,
            originalOccurrencePairIf,
            liftLiteral, negate] <;> aesop
      · have restNil : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp only [List.length_cons] at sourceWidth
          omega
        subst rest
        simp [clauseClauses, disjunctionGadget,
          auxiliary, liftLiteral, negate] at generatedMember
        rcases generatedMember with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp_all [clauseOriginalOccurrencePairs,
            originalOccurrencePairIf,
            liftLiteral, negate] <;> aesop

end PeriodicOneInThree

namespace PeriodicOneInThreePositioned

def formulaClauseMetadataFrom
    {Variable : Type*}
    (sourceStart : Nat)
    (clauses : List (PositionedPeriodicClause Variable)) :
    List (ClauseMetadata Variable) :=
  clauses.zipIdx sourceStart |>.flatMap fun taggedSource =>
    clauseMetadataFor taggedSource.2 taggedSource.1

@[simp]
theorem formulaClauseMetadataFrom_zero
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    formulaClauseMetadataFrom 0 source.clauses =
      formulaClauseMetadata source := by
  rfl

theorem clauseMetadataFor_lookup_localClauseIndex
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {index : Nat} {metadata : ClauseMetadata Variable}
    (lookup :
      (clauseMetadataFor
        sourceClauseIndex sourceClause)[index]? =
          some metadata) :
    metadata.localClauseIndex = index := by
  have mapped :=
    congrArg
      (Option.map ClauseMetadata.localClauseIndex) lookup
  simp [clauseMetadataFor] at mapped
  exact mapped.2.symm

theorem originalOccurrencePair_of_metadataLookup
    {Variable : Type*} [DecidableEq Variable]
    (atom : Variable) (outputStart sourceStart : Nat)
    (clauses : List (PositionedPeriodicClause Variable))
    (sourceWidth :
      ∀ clause ∈ clauses, clause.literals.length ≤ 3)
    (sourceDistinct :
      ∀ clause ∈ clauses,
        (clause.literals.map PeriodicLiteral.atom).Nodup)
    {metadataIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadataFrom
        sourceStart clauses)[metadataIndex]? =
          some metadata)
    {outputLiteral :
      PeriodicLiteral (OneInThreeVariable Variable)}
    {outputLiteralIndex : Nat}
    (outputMember :
      (outputLiteral, outputLiteralIndex) ∈
        metadata.clause.literals.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (outputAtom : outputLiteral.atom = .inl atom)
    (sourceAtom : sourceLiteral.atom = atom) :
    ((outputLiteral, outputStart + metadataIndex,
        outputLiteralIndex),
      (sourceLiteral, metadata.sourceClauseIndex,
        sourceLiteralIndex)) ∈
      PeriodicOneInThree.formulaOriginalOccurrencePairsFrom
        atom outputStart sourceStart
        (clauses.map PositionedPeriodicClause.literals) := by
  induction clauses generalizing
      outputStart sourceStart metadataIndex metadata with
  | nil =>
      simp [formulaClauseMetadataFrom] at metadataLookup
  | cons clause rest induction =>
      rw [show
        formulaClauseMetadataFrom sourceStart (clause :: rest) =
          clauseMetadataFor sourceStart clause ++
            formulaClauseMetadataFrom (sourceStart + 1) rest by
          simp [formulaClauseMetadataFrom]]
        at metadataLookup
      by_cases inHead :
          metadataIndex <
            (clauseMetadataFor sourceStart clause).length
      · rw [List.getElem?_append_left inHead] at metadataLookup
        have metadataMember :
            metadata ∈ clauseMetadataFor sourceStart clause :=
          List.mem_iff_getElem?.mpr
            ⟨metadataIndex, metadataLookup⟩
        have valid :=
          clauseMetadataFor_valid
            sourceStart clause metadataMember
        have metadataLocalIndex :
            metadata.localClauseIndex = metadataIndex := by
          exact clauseMetadataFor_lookup_localClauseIndex
            sourceStart clause metadataLookup
        have erasedGeneratedMember :
            (metadata.clause.literals,
                metadata.localClauseIndex) ∈
              (PeriodicOneInThree.clauseClauses
                metadata.sourceClauseIndex
                metadata.sourceClause.literals).zipIdx := by
          have positionedLookup :
              (clauseGadget metadata.sourceClauseIndex
                metadata.sourceClause)[metadata.localClauseIndex]? =
                  some metadata.clause :=
            by
              simpa [valid.1, valid.2.1] using
                (List.mem_zipIdx_iff_getElem?).mp valid.2.2
          have erasedLookup :
              ((clauseGadget metadata.sourceClauseIndex
                  metadata.sourceClause).map
                    PositionedPeriodicClause.literals)[
                metadata.localClauseIndex]? =
                some metadata.clause.literals := by
            rw [List.getElem?_map, positionedLookup]
            rfl
          rw [clauseGadget_literals] at erasedLookup
          exact
            List.mem_zipIdx_iff_getElem?.mpr erasedLookup
        have localPair :=
          PeriodicOneInThree.clauseOriginalOccurrencePairs_mem_of_members
            atom outputStart metadata.sourceClauseIndex
            metadata.sourceClause.literals
            (by
              simpa [valid.1] using
                sourceWidth clause (by simp))
            (by
              simpa [valid.1] using
                sourceDistinct clause (by simp))
            erasedGeneratedMember outputMember sourceMember
            outputAtom sourceAtom
        change
          ((outputLiteral, outputStart + metadataIndex,
              outputLiteralIndex),
            (sourceLiteral, metadata.sourceClauseIndex,
              sourceLiteralIndex)) ∈
            PeriodicOneInThree.formulaOriginalOccurrencePairsFrom
              atom outputStart sourceStart
              (clause.literals ::
                rest.map PositionedPeriodicClause.literals)
        rw [PeriodicOneInThree.formulaOriginalOccurrencePairsFrom]
        apply List.mem_append.mpr
        left
        simpa [valid.1, valid.2.1, metadataLocalIndex]
          using localPair
      · have headLengthLe :
            (clauseMetadataFor sourceStart clause).length ≤
              metadataIndex :=
          Nat.le_of_not_gt inHead
        have headLengthEq :
            (clauseMetadataFor sourceStart clause).length =
              (PeriodicOneInThree.clauseClauses
                sourceStart clause.literals).length := by
          simp [clauseMetadataFor, clauseGadget]
        have periodicHeadLengthLe :
            (PeriodicOneInThree.clauseClauses
              sourceStart clause.literals).length ≤
                metadataIndex := by
          simpa [headLengthEq] using headLengthLe
        rw [List.getElem?_append_right headLengthLe]
          at metadataLookup
        have tailPair :=
          induction
            (outputStart +
              (clauseMetadataFor sourceStart clause).length)
            (sourceStart + 1)
            (by
              intro current member
              exact sourceWidth current (by simp [member]))
            (by
              intro current member
              exact sourceDistinct current (by simp [member]))
            metadataLookup outputMember sourceMember
            
        change
          ((outputLiteral, outputStart + metadataIndex,
              outputLiteralIndex),
            (sourceLiteral, metadata.sourceClauseIndex,
              sourceLiteralIndex)) ∈
            PeriodicOneInThree.formulaOriginalOccurrencePairsFrom
              atom outputStart sourceStart
              (clause.literals ::
                rest.map PositionedPeriodicClause.literals)
        rw [PeriodicOneInThree.formulaOriginalOccurrencePairsFrom]
        apply List.mem_append.mpr
        right
        simpa [headLengthEq,
          Nat.add_sub_of_le periodicHeadLengthLe,
          Nat.add_assoc] using tailPair

/-- A flattened positioned Figure 9 incidence and the source incidence
carried by its metadata form one of the explicit order-preserving
occurrence pairs. -/
theorem originalOccurrencePair_of_formulaMetadataLookup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (atom : Variable)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? =
        some metadata)
    {outputLiteral :
      PeriodicLiteral (OneInThreeVariable Variable)}
    {outputLiteralIndex : Nat}
    (outputMember :
      (outputLiteral, outputLiteralIndex) ∈
        metadata.clause.literals.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx)
    (outputAtom : outputLiteral.atom = .inl atom)
    (sourceAtom : sourceLiteral.atom = atom) :
    ((outputLiteral, clauseIndex, outputLiteralIndex),
      (sourceLiteral, metadata.sourceClauseIndex,
        sourceLiteralIndex)) ∈
      PeriodicOneInThree.formulaOriginalOccurrencePairs
        source.erase atom := by
  have paired :=
    originalOccurrencePair_of_metadataLookup
      atom 0 0 source.clauses
      (by
        intro clause clauseMember
        exact sourceWidth clause.literals
          (List.mem_map.mpr
            ⟨clause, clauseMember, rfl⟩))
      sourceDistinct metadataLookup outputMember sourceMember
      outputAtom sourceAtom
  simpa [PeriodicOneInThree.formulaOriginalOccurrencePairs,
    PositionedPeriodicCNF.erase] using paired

end PeriodicOneInThreePositioned
end LeanTrominoes
