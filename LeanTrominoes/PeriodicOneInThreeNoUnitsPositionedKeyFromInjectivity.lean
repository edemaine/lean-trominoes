import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedOriginalOccurrenceProvenance

/-!
# Key injectivity for shifted unit-elimination metadata

Composed Figure Nine blocks enumerate unit-elimination metadata from a
nonzero global Figure Nine clause index.  Source and local clause indices
remain a duplicate-free key under that shift.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- Shifted `zipIdx` source indices remain pairwise distinct. -/
private theorem zipIdx_from_map_snd_nodup
    {α : Type*} (start : Nat) (values : List α) :
    ((values.zipIdx start).map Prod.snd).Nodup := by
  simp [List.nodup_range']

/-- Source-block/local-clause keys are pairwise distinct in metadata
enumerated from any starting source index. -/
theorem formulaClauseMetadataFrom_keys_nodup
    {Variable : Type*}
    (sourceStart : Nat)
    (clauses : List (PositionedPeriodicClause Variable)) :
    ((formulaClauseMetadataFrom sourceStart clauses).map
        ClauseMetadata.key).Nodup := by
  have sourceIndicesPairwise :
      (clauses.zipIdx sourceStart).Pairwise
        (fun first second => first.2 ≠ second.2) := by
    rw [← List.pairwise_map]
    exact zipIdx_from_map_snd_nodup sourceStart clauses
  rw [formulaClauseMetadataFrom, List.map_flatMap,
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

/-- Equal keys returned by two shifted metadata lookups identify the same
flattened local index. -/
theorem formulaClauseMetadataFrom_lookup_key_injective
    {Variable : Type*}
    (sourceStart : Nat)
    (clauses : List (PositionedPeriodicClause Variable))
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    {firstIndex secondIndex : Nat}
    (firstLookup :
      (formulaClauseMetadataFrom sourceStart clauses)[firstIndex]? =
        some firstMetadata)
    (secondLookup :
      (formulaClauseMetadataFrom sourceStart clauses)[secondIndex]? =
        some secondMetadata)
    (keysEqual : firstMetadata.key = secondMetadata.key) :
    firstIndex = secondIndex := by
  have firstKeyLookup :
      ((formulaClauseMetadataFrom sourceStart clauses).map
        ClauseMetadata.key)[firstIndex]? =
          some firstMetadata.key := by
    rw [List.getElem?_map, firstLookup]
    rfl
  have secondKeyLookup :
      ((formulaClauseMetadataFrom sourceStart clauses).map
        ClauseMetadata.key)[secondIndex]? =
          some secondMetadata.key := by
    rw [List.getElem?_map, secondLookup]
    rfl
  rcases List.getElem?_eq_some_iff.mp firstKeyLookup with
    ⟨firstIndexLt, firstKeyAt⟩
  rcases List.getElem?_eq_some_iff.mp secondKeyLookup with
    ⟨secondIndexLt, secondKeyAt⟩
  have keyValuesEqual :
      ((formulaClauseMetadataFrom sourceStart clauses).map
        ClauseMetadata.key)[firstIndex]'firstIndexLt =
      ((formulaClauseMetadataFrom sourceStart clauses).map
        ClauseMetadata.key)[secondIndex]'secondIndexLt := by
    rw [firstKeyAt, secondKeyAt, keysEqual]
  exact
    ((formulaClauseMetadataFrom_keys_nodup sourceStart clauses).getElem_inj_iff
      (hi := firstIndexLt) (hj := secondIndexLt)).mp keyValuesEqual

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
