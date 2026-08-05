import LeanTrominoes.PeriodicOneInThreePositionedIndex

/-!
# Key injectivity for positioned Figure Nine metadata

The positioned Figure Nine formula is a flat map of variable-size clause
blocks.  The pair consisting of the source-clause presentation index and the
local generated-clause index uniquely identifies an entry of that flattened
metadata list.  Unit elimination already exposes the analogous fact; this
file supplies it for the first replacement layer.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- Source-block and local-clause coordinates of one Figure Nine metadata
entry. -/
def ClauseMetadata.key
    {Variable : Type*}
    (metadata : ClauseMetadata Variable) : Nat × Nat :=
  (metadata.sourceClauseIndex, metadata.localClauseIndex)

/-- Local generated-clause indices do not repeat inside one source block. -/
theorem clauseMetadataFor_keys_nodup
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    ((clauseMetadataFor sourceClauseIndex sourceClause).map
        ClauseMetadata.key).Nodup := by
  let clauses := clauseGadget sourceClauseIndex sourceClause
  have indicesNodup :
      (clauses.zipIdx.map Prod.snd).Nodup :=
    List.nodup_zipIdx_map_snd clauses
  have keyedNodup :=
    indicesNodup.map
      (fun first second equal =>
        congrArg Prod.snd equal :
        Function.Injective fun localClauseIndex : Nat =>
          (sourceClauseIndex, localClauseIndex))
  unfold clauseMetadataFor
  rw [List.map_map]
  change
    (clauses.zipIdx.map
      ((fun localClauseIndex =>
        (sourceClauseIndex, localClauseIndex)) ∘ Prod.snd)).Nodup
  rw [List.map_map] at keyedNodup
  exact keyedNodup

/-- Source-block/local-clause keys are pairwise distinct across the complete
flattened Figure Nine metadata enumeration. -/
theorem formulaClauseMetadata_keys_nodup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    ((formulaClauseMetadata source).map
        ClauseMetadata.key).Nodup := by
  have sourceIndicesPairwise :
      source.clauses.zipIdx.Pairwise
        (fun first second => first.2 ≠ second.2) := by
    rw [← List.pairwise_map]
    exact List.nodup_zipIdx_map_snd source.clauses
  rw [formulaClauseMetadata, List.map_flatMap,
    List.nodup_flatMap]
  constructor
  · intro taggedSource _
    exact clauseMetadataFor_keys_nodup
      taggedSource.2 taggedSource.1
  · exact sourceIndicesPairwise.imp fun
      {first second} sourceIndexNe => by
        change List.Disjoint _ _
        rw [List.disjoint_left]
        intro key firstKeyMember secondKeyMember
        rcases List.mem_map.mp firstKeyMember with
          ⟨firstMetadata, firstMetadataMember, firstKeyEqual⟩
        rcases List.mem_map.mp secondKeyMember with
          ⟨secondMetadata, secondMetadataMember, secondKeyEqual⟩
        have firstValid :=
          clauseMetadataFor_valid
            first.2 first.1 firstMetadataMember
        have secondValid :=
          clauseMetadataFor_valid
            second.2 second.1 secondMetadataMember
        have metadataSourceIndicesEqual :=
          congrArg Prod.fst
            (firstKeyEqual.trans secondKeyEqual.symm)
        apply sourceIndexNe
        simpa [ClauseMetadata.key, firstValid.2.1,
          secondValid.2.1] using metadataSourceIndicesEqual

/-- Equal source-block/local-clause keys returned by two metadata lookups
force the corresponding global generated-clause indices to be equal. -/
theorem formulaClauseMetadata_lookup_key_injective
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstLookup :
      (formulaClauseMetadata source)[firstClauseIndex]? =
        some firstMetadata)
    (secondLookup :
      (formulaClauseMetadata source)[secondClauseIndex]? =
        some secondMetadata)
    (keysEqual : firstMetadata.key = secondMetadata.key) :
    firstClauseIndex = secondClauseIndex := by
  have firstKeyLookup :
      ((formulaClauseMetadata source).map
        ClauseMetadata.key)[firstClauseIndex]? =
          some firstMetadata.key := by
    rw [List.getElem?_map, firstLookup]
    rfl
  have secondKeyLookup :
      ((formulaClauseMetadata source).map
        ClauseMetadata.key)[secondClauseIndex]? =
          some secondMetadata.key := by
    rw [List.getElem?_map, secondLookup]
    rfl
  rcases List.getElem?_eq_some_iff.mp firstKeyLookup with
    ⟨firstIndexLt, firstKeyAt⟩
  rcases List.getElem?_eq_some_iff.mp secondKeyLookup with
    ⟨secondIndexLt, secondKeyAt⟩
  have keyValuesEqual :
      ((formulaClauseMetadata source).map
        ClauseMetadata.key)[firstClauseIndex]'firstIndexLt =
      ((formulaClauseMetadata source).map
        ClauseMetadata.key)[secondClauseIndex]'secondIndexLt := by
    rw [firstKeyAt, secondKeyAt, keysEqual]
  exact
    ((formulaClauseMetadata_keys_nodup source).getElem_inj_iff
      (hi := firstIndexLt) (hj := secondIndexLt)).mp keyValuesEqual

end PeriodicOneInThreePositioned
end LeanTrominoes
