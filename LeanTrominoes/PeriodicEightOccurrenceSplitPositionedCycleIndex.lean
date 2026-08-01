import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedCycleDrawing

/-!
# Indexing the positioned occurrence-splitting cycles

The positioned fixed-eight formula stores all implication rings in one
`flatMap`.  A global route family must recover both the source atom and the
local Figure 7 clause index from a clause's position in that flattened list.

This module keeps that indexing information in a parallel metadata list and
proves that projecting its clauses gives exactly the existing flattened
formula.  Thus later route definitions can use list lookup directly, without
reconstructing the fixed block size arithmetically.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

/-- The data needed to select a certified route for one positioned cycle
clause. -/
structure CycleClauseMetadata
    (Variable : Type*) where
  clause :
    PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable)
  atom : Variable
  localClauseIndex : Nat

/-- The source atom and local Figure 7 clause index uniquely identify an
entry in the flattened cycle metadata. -/
def CycleClauseMetadata.key
    {Variable : Type*}
    (metadata : CycleClauseMetadata Variable) :
    Variable × Nat :=
  (metadata.atom, metadata.localClauseIndex)

/-- Index every implication clause in one atom's local cycle block. -/
def cycleClauseMetadataFor
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    List (CycleClauseMetadata Variable) :=
  (cycleClausesFor sourcePlacement atom).zipIdx.map
    fun taggedClause =>
      ⟨taggedClause.1, atom, taggedClause.2⟩

/-- Metadata parallel to the flattened list of every positioned cycle
clause. -/
def allCycleClauseMetadata
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    List (CycleClauseMetadata Variable) :=
  (PeriodicThreeSATThree.sourceVariables source.erase).flatMap
    (cycleClauseMetadataFor sourcePlacement)

@[simp]
theorem cycleClauseMetadataFor_clauses
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    (cycleClauseMetadataFor sourcePlacement atom).map
        CycleClauseMetadata.clause =
      cycleClausesFor sourcePlacement atom := by
  simp [cycleClauseMetadataFor, List.map_map,
    Function.comp_def]

/-- Metadata stored in one atom's block points back to a genuine clause at
its recorded local index. -/
theorem cycleClauseMetadataFor_valid
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable)
    {metadata : CycleClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        cycleClauseMetadataFor sourcePlacement atom) :
    metadata.atom = atom ∧
      (metadata.clause, metadata.localClauseIndex) ∈
        (cycleClausesFor sourcePlacement atom).zipIdx := by
  rw [cycleClauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember,
      metadataEqual⟩
  subst metadata
  exact ⟨rfl, taggedClauseMember⟩

/-- Local clause indices do not repeat within one atom's cycle block. -/
theorem cycleClauseMetadataFor_keys_nodup
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    ((cycleClauseMetadataFor sourcePlacement atom).map
      CycleClauseMetadata.key).Nodup := by
  let clauses := cycleClausesFor sourcePlacement atom
  have indicesNodup :
      (clauses.zipIdx.map Prod.snd).Nodup :=
    List.nodup_zipIdx_map_snd clauses
  have keyedNodup :=
    indicesNodup.map
      (fun first second equal =>
        congrArg Prod.snd equal :
        Function.Injective fun localClauseIndex : Nat =>
          (atom, localClauseIndex))
  unfold cycleClauseMetadataFor
  rw [List.map_map]
  change
    (clauses.zipIdx.map
      ((fun localClauseIndex => (atom, localClauseIndex)) ∘
        Prod.snd)).Nodup
  rw [List.map_map] at keyedNodup
  exact keyedNodup

/-- Forgetting the indexing metadata recovers the existing positioned cycle
list definitionally block-for-block. -/
@[simp]
theorem allCycleClauseMetadata_clauses
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    (allCycleClauseMetadata source sourcePlacement).map
        CycleClauseMetadata.clause =
      allCycleClauses source sourcePlacement := by
  simp [allCycleClauseMetadata, allCycleClauses,
    List.map_flatMap]

/-- Every entry in the global metadata list retains the local cycle
membership certified by its atom and local index. -/
theorem allCycleClauseMetadata_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {metadata : CycleClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        allCycleClauseMetadata source sourcePlacement) :
    (metadata.clause, metadata.localClauseIndex) ∈
      (cycleClausesFor
        sourcePlacement metadata.atom).zipIdx := by
  rw [allCycleClauseMetadata,
    List.mem_flatMap] at metadataMember
  rcases metadataMember with
    ⟨atom, _atomMember, metadataMember⟩
  have valid :=
    cycleClauseMetadataFor_valid
      sourcePlacement atom metadataMember
  simpa [valid.1] using valid.2

/-- The `(source atom, local clause)` keys of the flattened cycle metadata
are pairwise distinct. -/
theorem allCycleClauseMetadata_keys_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    ((allCycleClauseMetadata source sourcePlacement).map
      CycleClauseMetadata.key).Nodup := by
  rw [allCycleClauseMetadata, List.map_flatMap,
    List.nodup_flatMap]
  constructor
  · intro atom _atomMember
    exact
      cycleClauseMetadataFor_keys_nodup
        sourcePlacement atom
  · exact
      (List.nodup_iff_pairwise_ne.mp
        (List.nodup_dedup _)).imp fun
          {firstAtom secondAtom} atomsDifferent => by
        change List.Disjoint _ _
        rw [List.disjoint_left]
        intro key firstKeyMember secondKeyMember
        rcases List.mem_map.mp firstKeyMember with
          ⟨firstMetadata, firstMetadataMember, rfl⟩
        rcases List.mem_map.mp secondKeyMember with
          ⟨secondMetadata, secondMetadataMember,
            secondKeyEqual⟩
        have firstAtomEqual :=
          (cycleClauseMetadataFor_valid
            sourcePlacement firstAtom
            firstMetadataMember).1
        have secondAtomEqual :=
          (cycleClauseMetadataFor_valid
            sourcePlacement secondAtom
            secondMetadataMember).1
        apply atomsDifferent
        exact
          firstAtomEqual.symm.trans
            ((congrArg Prod.fst secondKeyEqual).symm.trans
              secondAtomEqual)

/-- Equal atom/local-clause keys returned by two metadata lookups force the
two flattened cycle indices to be equal. -/
theorem allCycleClauseMetadata_lookup_key_injective
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstMetadata secondMetadata :
      CycleClauseMetadata Variable}
    {firstCycleIndex secondCycleIndex : Nat}
    (firstLookup :
      (allCycleClauseMetadata
        source sourcePlacement)[firstCycleIndex]? =
          some firstMetadata)
    (secondLookup :
      (allCycleClauseMetadata
        source sourcePlacement)[secondCycleIndex]? =
          some secondMetadata)
    (keysEqual :
      firstMetadata.key = secondMetadata.key) :
    firstCycleIndex = secondCycleIndex := by
  have firstKeyLookup :
      ((allCycleClauseMetadata source sourcePlacement).map
        CycleClauseMetadata.key)[firstCycleIndex]? =
          some firstMetadata.key := by
    rw [List.getElem?_map, firstLookup]
    rfl
  have secondKeyLookup :
      ((allCycleClauseMetadata source sourcePlacement).map
        CycleClauseMetadata.key)[secondCycleIndex]? =
          some secondMetadata.key := by
    rw [List.getElem?_map, secondLookup]
    rfl
  rcases List.getElem?_eq_some_iff.mp firstKeyLookup with
    ⟨firstIndexLt, firstKeyAt⟩
  rcases List.getElem?_eq_some_iff.mp secondKeyLookup with
    ⟨secondIndexLt, secondKeyAt⟩
  apply
    ((allCycleClauseMetadata_keys_nodup
      source sourcePlacement).getElem_inj_iff).mp
  rw [firstKeyAt, secondKeyAt, keysEqual]

/-- Looking up a genuine flattened cycle clause yields metadata carrying
that exact clause. -/
theorem allCycleClauseMetadata_lookup
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx) :
    ∃ metadata,
      (allCycleClauseMetadata
          source sourcePlacement)[cycleIndex]? =
        some metadata ∧
      metadata.clause = clause := by
  have clauseLookup :
      (allCycleClauses
          source sourcePlacement)[cycleIndex]? =
        some clause :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have projectedLookup :
      ((allCycleClauseMetadata source sourcePlacement).map
          CycleClauseMetadata.clause)[cycleIndex]? =
        some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simp only [Option.map_eq_some_iff] at projectedLookup
  exact projectedLookup

/-- A genuine flattened clause lookup also returns the local membership
invariant needed to apply the per-atom route certificate. -/
theorem allCycleClauseMetadata_lookup_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx) :
    ∃ metadata,
      (allCycleClauseMetadata
          source sourcePlacement)[cycleIndex]? =
        some metadata ∧
      metadata.clause = clause ∧
      (metadata.clause, metadata.localClauseIndex) ∈
        (cycleClausesFor
          sourcePlacement metadata.atom).zipIdx := by
  rcases allCycleClauseMetadata_lookup
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have metadataIndexLt :
      cycleIndex <
        (allCycleClauseMetadata
          source sourcePlacement).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (allCycleClauseMetadata
          source sourcePlacement)[cycleIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        allCycleClauseMetadata
          source sourcePlacement := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  exact
    ⟨metadata, metadataLookup, clauseEqual,
      allCycleClauseMetadata_valid
        source sourcePlacement metadataMember⟩

/-- The atom owning the cycle block at a flattened clause index, when that
index is valid. -/
def allCycleClauseAtom?
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (cycleIndex : Nat) :
    Option Variable :=
  (allCycleClauseMetadata
    source sourcePlacement)[cycleIndex]?.map
      CycleClauseMetadata.atom

/-- Route lookup for the flattened cycle suffix, indexed relative to the
start of that suffix. -/
def allCycleRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun cycleIndex literalIndex =>
    match
      (allCycleClauseMetadata
        source sourcePlacement)[cycleIndex]?
    with
    | none => []
    | some metadata =>
        positionedCycleRoutes sourcePlacement
          metadata.atom metadata.localClauseIndex literalIndex

/-- A genuine flattened cycle clause selects the certified route family
recorded by its metadata. -/
theorem allCycleRoutes_of_clause_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {cycleIndex : Nat}
    (clauseMember :
      (clause, cycleIndex) ∈
        (allCycleClauses source sourcePlacement).zipIdx)
    (literalIndex : Nat) :
    ∃ metadata : CycleClauseMetadata Variable,
      metadata.clause = clause ∧
      allCycleRoutes source sourcePlacement
          cycleIndex literalIndex =
        positionedCycleRoutes sourcePlacement
          metadata.atom metadata.localClauseIndex
          literalIndex := by
  rcases allCycleClauseMetadata_lookup
      source sourcePlacement clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  refine ⟨metadata, clauseEqual, ?_⟩
  simp [allCycleRoutes, metadataLookup]

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
