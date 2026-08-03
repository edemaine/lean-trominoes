import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineInstantiation
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedOriginalOccurrenceProvenance
import LeanTrominoes.PeriodicOneInThreePositionedOriginalOccurrenceProvenance

/-!
# Indexing the composed Figure 9 and unit-elimination replacement

The two positioned reductions flatten two variable-size layers of local
clause blocks.  This module enumerates the same output one original source
clause at a time.  Each final clause thereby retains:

* its original positioned source clause and presentation index;
* the global presentation index at which that source's Figure 9 block starts;
* its local presentation index in the complete composed block.

Projecting final clauses from the metadata recovers the actual two-stage
positioned formula exactly.  The local index is consequently also the clause
index used by the certified composed drawing.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

/-- Enumerate positioned Figure 9 blocks beginning at an arbitrary source
presentation index. -/
def figureNineClausesFrom
    {Variable : Type*}
    (sourceClauseIndex : Nat) :
    List (PositionedPeriodicClause Variable) →
      List
        (PositionedPeriodicClause
          (OneInThreeVariable Variable))
  | [] => []
  | sourceClause :: rest =>
      PeriodicOneInThreePositioned.clauseGadget
          sourceClauseIndex sourceClause ++
        figureNineClausesFrom
          (sourceClauseIndex + 1) rest

/-- Enumerate positioned unit-elimination blocks beginning at an arbitrary
Figure 9 presentation index. -/
def unitEliminationClausesFrom
    {Variable : Type*}
    (figureNineClauseIndex : Nat) :
    List (PositionedPeriodicClause Variable) →
      List
        (PositionedPeriodicClause
          (OneInThreeNoUnitVariable Variable))
  | [] => []
  | sourceClause :: rest =>
      PeriodicOneInThreeNoUnitsPositioned.clauseGadget
          figureNineClauseIndex sourceClause ++
        unitEliminationClausesFrom
          (figureNineClauseIndex + 1) rest

/-- Enumerate both transformations one original source block at a time,
threading the global Figure 9 presentation index between blocks. -/
def composedClausesFrom
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat) :
    List (PositionedPeriodicClause Variable) →
      List
        (PositionedPeriodicClause
          (OneInThreeNoUnitVariable
            (OneInThreeVariable Variable)))
  | [] => []
  | sourceClause :: rest =>
      let figureNineBlock :=
        PeriodicOneInThreePositioned.clauseGadget
          sourceClauseIndex sourceClause
      unitEliminationClausesFrom
          figureNineClauseStart figureNineBlock ++
        composedClausesFrom
          (sourceClauseIndex + 1)
          (figureNineClauseStart + figureNineBlock.length)
          rest

/-- Source and local indexing information for one final clause in the
composed replacement. -/
structure ClauseMetadata
    (Variable : Type*) where
  sourceClause : PositionedPeriodicClause Variable
  sourceClauseIndex : Nat
  figureNineClauseStart : Nat
  clause :
    PositionedPeriodicClause
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable))
  localClauseIndex : Nat

/-- The original source block and local final-clause index uniquely identify
an entry in the composed metadata list. -/
def ClauseMetadata.key
    {Variable : Type*}
    (metadata : ClauseMetadata Variable) : Nat × Nat :=
  (metadata.sourceClauseIndex, metadata.localClauseIndex)

/-- Index every final clause in one original source clause's complete
composed block. -/
def clauseMetadataFor
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    List (ClauseMetadata Variable) :=
  (unitEliminationClausesFrom
      figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget
        sourceClauseIndex sourceClause)).zipIdx.map
    fun taggedClause =>
      ⟨sourceClause, sourceClauseIndex,
        figureNineClauseStart,
        taggedClause.1, taggedClause.2⟩

/-- Metadata parallel to a recursively enumerated suffix of the composed
formula. -/
def formulaClauseMetadataFrom
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat) :
    List (PositionedPeriodicClause Variable) →
      List (ClauseMetadata Variable)
  | [] => []
  | sourceClause :: rest =>
      let figureNineBlock :=
        PeriodicOneInThreePositioned.clauseGadget
          sourceClauseIndex sourceClause
      clauseMetadataFor
          sourceClauseIndex figureNineClauseStart sourceClause ++
        formulaClauseMetadataFrom
          (sourceClauseIndex + 1)
          (figureNineClauseStart + figureNineBlock.length)
          rest

/-- Metadata parallel to the complete two-stage positioned formula. -/
def formulaClauseMetadata
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    List (ClauseMetadata Variable) :=
  formulaClauseMetadataFrom 0 0 source.clauses

theorem figureNineClausesFrom_eq_zipIdx
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable)) :
    figureNineClausesFrom sourceClauseIndex sourceClauses =
      (sourceClauses.zipIdx sourceClauseIndex).flatMap
        (fun taggedSource =>
          PeriodicOneInThreePositioned.clauseGadget
            taggedSource.2 taggedSource.1) := by
  induction sourceClauses generalizing sourceClauseIndex with
  | nil => simp [figureNineClausesFrom]
  | cons sourceClause rest induction =>
      simp [figureNineClausesFrom, induction,
        List.zipIdx_cons]

theorem unitEliminationClausesFrom_eq_zipIdx
    {Variable : Type*}
    (figureNineClauseIndex : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable)) :
    unitEliminationClausesFrom
        figureNineClauseIndex sourceClauses =
      (sourceClauses.zipIdx figureNineClauseIndex).flatMap
        (fun taggedSource =>
          PeriodicOneInThreeNoUnitsPositioned.clauseGadget
            taggedSource.2 taggedSource.1) := by
  induction sourceClauses generalizing figureNineClauseIndex with
  | nil => simp [unitEliminationClausesFrom]
  | cons sourceClause rest induction =>
      simp [unitEliminationClausesFrom, induction,
        List.zipIdx_cons]

/-- Equivalently, retain local indices in `zipIdx` and add a fixed global
offset when selecting each unit-elimination block. -/
theorem unitEliminationClausesFrom_eq_shiftedZipIdx
    {Variable : Type*}
    (globalStart localStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable)) :
    unitEliminationClausesFrom
        (globalStart + localStart) sourceClauses =
      (sourceClauses.zipIdx localStart).flatMap
        (fun taggedSource =>
          PeriodicOneInThreeNoUnitsPositioned.clauseGadget
            (globalStart + taggedSource.2) taggedSource.1) := by
  induction sourceClauses generalizing localStart with
  | nil => simp [unitEliminationClausesFrom]
  | cons sourceClause rest induction =>
      rw [unitEliminationClausesFrom, List.zipIdx_cons,
        List.flatMap_cons]
      have nextIndex :
          globalStart + localStart + 1 =
            globalStart + (localStart + 1) := by
        omega
      rw [nextIndex, induction]

/-- The common zero-based form of shifted local enumeration. -/
theorem unitEliminationClausesFrom_eq_localZipIdx
    {Variable : Type*}
    (globalStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable)) :
    unitEliminationClausesFrom globalStart sourceClauses =
      sourceClauses.zipIdx.flatMap
        (fun taggedSource =>
          PeriodicOneInThreeNoUnitsPositioned.clauseGadget
            (globalStart + taggedSource.2) taggedSource.1) := by
  simpa using
    unitEliminationClausesFrom_eq_shiftedZipIdx
      (Variable := Variable) globalStart 0 sourceClauses

/-- Unit-elimination enumeration splits across concatenated source lists,
with the second list's presentation indices shifted by the first length. -/
theorem unitEliminationClausesFrom_append
    {Variable : Type*}
    (figureNineClauseIndex : Nat)
    (initial remaining : List (PositionedPeriodicClause Variable)) :
    unitEliminationClausesFrom
        figureNineClauseIndex (initial ++ remaining) =
      unitEliminationClausesFrom
          figureNineClauseIndex initial ++
        unitEliminationClausesFrom
          (figureNineClauseIndex + initial.length) remaining := by
  induction initial generalizing figureNineClauseIndex with
  | nil => simp [unitEliminationClausesFrom]
  | cons sourceClause rest induction =>
      simp only [List.cons_append,
        unitEliminationClausesFrom, List.length_cons,
        List.append_assoc]
      rw [induction]
      have indexEqual :
          figureNineClauseIndex + 1 + rest.length =
            figureNineClauseIndex + (rest.length + 1) := by
        omega
      rw [indexEqual]

/-- Blockwise composed enumeration equals unit elimination applied after
the complete Figure 9 enumeration. -/
theorem composedClausesFrom_eq
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable)) :
    composedClausesFrom
        sourceClauseIndex figureNineClauseStart sourceClauses =
      unitEliminationClausesFrom
        figureNineClauseStart
        (figureNineClausesFrom
          sourceClauseIndex sourceClauses) := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [composedClausesFrom, figureNineClausesFrom,
        unitEliminationClausesFrom]
  | cons sourceClause rest induction =>
      rw [figureNineClausesFrom, composedClausesFrom,
        unitEliminationClausesFrom_append]
      rw [induction]

@[simp]
theorem clauseMetadataFor_clauses
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (clauseMetadataFor
      sourceClauseIndex figureNineClauseStart sourceClause).map
        ClauseMetadata.clause =
      unitEliminationClausesFrom
        figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          sourceClauseIndex sourceClause) := by
  simp [clauseMetadataFor, List.map_map,
    Function.comp_def]

@[simp]
theorem formulaClauseMetadataFrom_clauses
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable)) :
    (formulaClauseMetadataFrom
      sourceClauseIndex figureNineClauseStart sourceClauses).map
        ClauseMetadata.clause =
      composedClausesFrom
        sourceClauseIndex figureNineClauseStart sourceClauses := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [formulaClauseMetadataFrom, composedClausesFrom]
  | cons sourceClause rest induction =>
      simp [formulaClauseMetadataFrom, composedClausesFrom,
        induction]

/-- Forgetting the composed metadata recovers the actual two-stage
positioned formula exactly. -/
@[simp]
theorem formulaClauseMetadata_clauses
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    (formulaClauseMetadata source).map
        ClauseMetadata.clause =
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses := by
  rw [formulaClauseMetadata,
    formulaClauseMetadataFrom_clauses,
    composedClausesFrom_eq,
    figureNineClausesFrom_eq_zipIdx,
    unitEliminationClausesFrom_eq_zipIdx]
  rfl

/-- Embedding positions out of one enumerated composed block recovers the
exact embedded block used by the instantiated drawing. -/
@[simp]
theorem unitEliminationClausesFrom_embed
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (unitEliminationClausesFrom
      figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget
        sourceClauseIndex sourceClause)).map
          PlanarOneInThreeNoUnits.embedPositionedClause =
      composedClauseGadget
        sourceClauseIndex figureNineClauseStart sourceClause := by
  rw [unitEliminationClausesFrom_eq_localZipIdx]
  simp [composedClauseGadget, List.map_flatMap]

/-- A genuine positioned local clause remains at the same local index after
forgetting its position for the composed drawing. -/
theorem localClauseMember_embedded
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {localClauseIndex : Nat}
    (clauseMember :
      (clause, localClauseIndex) ∈
        (unitEliminationClausesFrom
          figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            sourceClauseIndex sourceClause)).zipIdx) :
    (PlanarOneInThreeNoUnits.embedPositionedClause clause,
        localClauseIndex) ∈
      (composedClauseGadget
        sourceClauseIndex figureNineClauseStart sourceClause).zipIdx := by
  rw [← unitEliminationClausesFrom_embed]
  apply List.mem_zipIdx_iff_getElem?.mpr
  rw [List.getElem?_map,
    (List.mem_zipIdx_iff_getElem?).mp clauseMember]
  rfl

/-- A local metadata entry retains its source and its genuine clause index
inside that source's composed block. -/
theorem clauseMetadataFor_valid
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ clauseMetadataFor
        sourceClauseIndex figureNineClauseStart sourceClause) :
    metadata.sourceClause = sourceClause ∧
      metadata.sourceClauseIndex = sourceClauseIndex ∧
      metadata.figureNineClauseStart = figureNineClauseStart ∧
      (metadata.clause, metadata.localClauseIndex) ∈
        (unitEliminationClausesFrom
          figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            sourceClauseIndex sourceClause)).zipIdx := by
  rw [clauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  exact ⟨rfl, rfl, rfl, taggedClauseMember⟩

/-- Local composed-clause indices do not repeat inside one source block. -/
theorem clauseMetadataFor_keys_nodup
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    ((clauseMetadataFor
      sourceClauseIndex figureNineClauseStart sourceClause).map
        ClauseMetadata.key).Nodup := by
  let clauses :=
    unitEliminationClausesFrom
      figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget
        sourceClauseIndex sourceClause)
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

/-- Every source index in a metadata suffix is at least the suffix's initial
source index. -/
theorem formulaClauseMetadataFrom_sourceClauseIndex_le
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable))
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadataFrom
        sourceClauseIndex figureNineClauseStart sourceClauses) :
    sourceClauseIndex ≤ metadata.sourceClauseIndex := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [formulaClauseMetadataFrom] at metadataMember
  | cons sourceClause rest induction =>
      rw [formulaClauseMetadataFrom,
        List.mem_append] at metadataMember
      rcases metadataMember with headMember | tailMember
      · have valid :=
          clauseMetadataFor_valid
            sourceClauseIndex figureNineClauseStart
            sourceClause headMember
        simp [valid.2.1]
      · have tailBound :=
          induction
            (sourceClauseIndex := sourceClauseIndex + 1)
            (figureNineClauseStart :=
              figureNineClauseStart +
                (PeriodicOneInThreePositioned.clauseGadget
                  sourceClauseIndex sourceClause).length)
            tailMember
        omega

/-- Within one metadata suffix, the original source presentation index
uniquely determines both the source clause and the global start of its
Figure 9 block. -/
theorem formulaClauseMetadataFrom_sourceBlock_eq
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable))
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    (firstMember :
      firstMetadata ∈ formulaClauseMetadataFrom
        sourceClauseIndex figureNineClauseStart sourceClauses)
    (secondMember :
      secondMetadata ∈ formulaClauseMetadataFrom
        sourceClauseIndex figureNineClauseStart sourceClauses)
    (sourceIndicesEqual :
      firstMetadata.sourceClauseIndex =
        secondMetadata.sourceClauseIndex) :
    firstMetadata.sourceClause = secondMetadata.sourceClause ∧
      firstMetadata.figureNineClauseStart =
        secondMetadata.figureNineClauseStart := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [formulaClauseMetadataFrom] at firstMember
  | cons sourceClause rest induction =>
      rw [formulaClauseMetadataFrom,
        List.mem_append] at firstMember secondMember
      rcases firstMember with firstHead | firstTail
      · have firstValid :=
          clauseMetadataFor_valid
            sourceClauseIndex figureNineClauseStart
            sourceClause firstHead
        rcases secondMember with secondHead | secondTail
        · have secondValid :=
            clauseMetadataFor_valid
              sourceClauseIndex figureNineClauseStart
              sourceClause secondHead
          exact
            ⟨firstValid.1.trans secondValid.1.symm,
              firstValid.2.2.1.trans
                secondValid.2.2.1.symm⟩
        · have secondBound :=
            formulaClauseMetadataFrom_sourceClauseIndex_le
              (sourceClauseIndex + 1)
              (figureNineClauseStart +
                (PeriodicOneInThreePositioned.clauseGadget
                  sourceClauseIndex sourceClause).length)
              rest secondTail
          rw [firstValid.2.1] at sourceIndicesEqual
          omega
      · have firstBound :=
          formulaClauseMetadataFrom_sourceClauseIndex_le
            (sourceClauseIndex + 1)
            (figureNineClauseStart +
              (PeriodicOneInThreePositioned.clauseGadget
                sourceClauseIndex sourceClause).length)
            rest firstTail
        rcases secondMember with secondHead | secondTail
        · have secondValid :=
            clauseMetadataFor_valid
              sourceClauseIndex figureNineClauseStart
              sourceClause secondHead
          rw [secondValid.2.1] at sourceIndicesEqual
          omega
        · exact
            induction
              (sourceClauseIndex := sourceClauseIndex + 1)
              (figureNineClauseStart :=
                figureNineClauseStart +
                  (PeriodicOneInThreePositioned.clauseGadget
                    sourceClauseIndex sourceClause).length)
              firstTail secondTail

/-- The `(source block, local clause)` keys of the complete metadata
enumeration are pairwise distinct. -/
theorem formulaClauseMetadataFrom_keys_nodup
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable)) :
    ((formulaClauseMetadataFrom
      sourceClauseIndex figureNineClauseStart sourceClauses).map
        ClauseMetadata.key).Nodup := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [formulaClauseMetadataFrom]
  | cons sourceClause rest induction =>
      rw [formulaClauseMetadataFrom, List.map_append,
        List.nodup_append]
      refine
        ⟨clauseMetadataFor_keys_nodup
            sourceClauseIndex figureNineClauseStart sourceClause,
          induction
            (sourceClauseIndex := sourceClauseIndex + 1)
            (figureNineClauseStart :=
              figureNineClauseStart +
                (PeriodicOneInThreePositioned.clauseGadget
                  sourceClauseIndex sourceClause).length),
          ?_⟩
      intro headKey headKeyMember tailKey tailKeyMember
      rcases List.mem_map.mp headKeyMember with
        ⟨headMetadata, headMetadataMember, headKeyEqual⟩
      rcases List.mem_map.mp tailKeyMember with
        ⟨tailMetadata, tailMetadataMember, tailKeyEqual⟩
      have headValid :=
        clauseMetadataFor_valid
          sourceClauseIndex figureNineClauseStart
          sourceClause headMetadataMember
      have tailBound :=
        formulaClauseMetadataFrom_sourceClauseIndex_le
          (sourceClauseIndex + 1)
          (figureNineClauseStart +
            (PeriodicOneInThreePositioned.clauseGadget
              sourceClauseIndex sourceClause).length)
          rest tailMetadataMember
      intro keysEqual
      have sourceIndicesEqual :
          headMetadata.sourceClauseIndex =
            tailMetadata.sourceClauseIndex := by
        exact congrArg Prod.fst
          (headKeyEqual.trans
            (keysEqual.trans tailKeyEqual.symm))
      rw [headValid.2.1] at sourceIndicesEqual
      omega

/-- Complete composed metadata keys are pairwise distinct. -/
theorem formulaClauseMetadata_keys_nodup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    ((formulaClauseMetadata source).map
        ClauseMetadata.key).Nodup := by
  exact formulaClauseMetadataFrom_keys_nodup
    0 0 source.clauses

/-- In the complete metadata list, equal original source indices identify
the same source clause and Figure 9 block start. -/
theorem formulaClauseMetadata_sourceBlock_eq
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {firstMetadata secondMetadata : ClauseMetadata Variable}
    (firstMember :
      firstMetadata ∈ formulaClauseMetadata source)
    (secondMember :
      secondMetadata ∈ formulaClauseMetadata source)
    (sourceIndicesEqual :
      firstMetadata.sourceClauseIndex =
        secondMetadata.sourceClauseIndex) :
    firstMetadata.sourceClause = secondMetadata.sourceClause ∧
      firstMetadata.figureNineClauseStart =
        secondMetadata.figureNineClauseStart := by
  exact formulaClauseMetadataFrom_sourceBlock_eq
    0 0 source.clauses firstMember secondMember sourceIndicesEqual

/-- Equal source-block/local-clause keys returned by two metadata lookups
force the two global final-clause indices to be equal. -/
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

/-- Every global metadata entry retains a genuine original source-clause
membership and a genuine local composed-clause membership. -/
theorem formulaClauseMetadataFrom_valid
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable))
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadataFrom
        sourceClauseIndex figureNineClauseStart sourceClauses) :
    (metadata.sourceClause,
        metadata.sourceClauseIndex) ∈
      sourceClauses.zipIdx sourceClauseIndex ∧
    (metadata.clause, metadata.localClauseIndex) ∈
      (unitEliminationClausesFrom
        metadata.figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex
          metadata.sourceClause)).zipIdx := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [formulaClauseMetadataFrom] at metadataMember
  | cons sourceClause rest induction =>
      rw [formulaClauseMetadataFrom,
        List.mem_append] at metadataMember
      rcases metadataMember with headMember | tailMember
      · have valid :=
          clauseMetadataFor_valid
            sourceClauseIndex figureNineClauseStart
            sourceClause headMember
        constructor
        · simp [valid.1, valid.2.1,
            List.zipIdx_cons]
        · simpa [valid.1, valid.2.1,
            valid.2.2.1] using valid.2.2.2
      · have valid :=
          induction
            (sourceClauseIndex :=
              sourceClauseIndex + 1)
            (figureNineClauseStart :=
              figureNineClauseStart +
                (PeriodicOneInThreePositioned.clauseGadget
                  sourceClauseIndex sourceClause).length)
            tailMember
        constructor
        · simp only [List.zipIdx_cons, List.mem_cons]
          exact Or.inr valid.1
        · exact valid.2

/-- Reindex a genuine zero-based list occurrence from an arbitrary starting
index. -/
theorem mem_zipIdx_from
    {α : Type*}
    (start : Nat)
    (values : List α)
    {value : α}
    {index : Nat}
    (member : (value, index) ∈ values.zipIdx) :
    (value, start + index) ∈ values.zipIdx start := by
  rw [List.zipIdx_eq_map_add]
  exact List.mem_map.mpr
    ⟨(value, index), member, rfl⟩

/-- The stored start of a composed metadata block converts every local
Figure 9 clause index into its genuine index in the recursively flattened
first-stage formula. -/
theorem formulaClauseMetadataFrom_figureNineClause_member
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable))
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadataFrom
        sourceClauseIndex figureNineClauseStart sourceClauses)
    {figureNineClause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {localClauseIndex : Nat}
    (figureNineClauseMember :
      (figureNineClause, localClauseIndex) ∈
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex
          metadata.sourceClause).zipIdx) :
    (figureNineClause,
        metadata.figureNineClauseStart + localClauseIndex) ∈
      (figureNineClausesFrom
        sourceClauseIndex sourceClauses).zipIdx
          figureNineClauseStart := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [formulaClauseMetadataFrom] at metadataMember
  | cons sourceClause rest induction =>
      rw [formulaClauseMetadataFrom,
        List.mem_append] at metadataMember
      rw [figureNineClausesFrom, List.zipIdx_append,
        List.mem_append]
      rcases metadataMember with headMember | tailMember
      · left
        have valid :=
          clauseMetadataFor_valid
            sourceClauseIndex figureNineClauseStart
            sourceClause headMember
        simpa [valid.1, valid.2.1, valid.2.2.1] using
          mem_zipIdx_from figureNineClauseStart
            (PeriodicOneInThreePositioned.clauseGadget
              metadata.sourceClauseIndex metadata.sourceClause)
            figureNineClauseMember
      · right
        exact induction
          (sourceClauseIndex := sourceClauseIndex + 1)
          (figureNineClauseStart :=
            figureNineClauseStart +
                (PeriodicOneInThreePositioned.clauseGadget
                  sourceClauseIndex sourceClause).length)
          tailMember

/-- The same local Figure 9 occurrence determines the exact standard
first-stage metadata entry, not just its projected generated clause. -/
theorem formulaClauseMetadataFrom_figureNineMetadata_member
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable))
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadataFrom
        sourceClauseIndex figureNineClauseStart sourceClauses)
    {figureNineClause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {localClauseIndex : Nat}
    (figureNineClauseMember :
      (figureNineClause, localClauseIndex) ∈
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex
          metadata.sourceClause).zipIdx) :
    ((⟨metadata.sourceClause, metadata.sourceClauseIndex,
        figureNineClause, localClauseIndex⟩ :
        PeriodicOneInThreePositioned.ClauseMetadata Variable),
      metadata.figureNineClauseStart + localClauseIndex) ∈
      (PeriodicOneInThreePositioned.formulaClauseMetadataFrom
        sourceClauseIndex sourceClauses).zipIdx
          figureNineClauseStart := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart with
  | nil =>
      simp [formulaClauseMetadataFrom] at metadataMember
  | cons sourceClause rest induction =>
      rw [formulaClauseMetadataFrom,
        List.mem_append] at metadataMember
      rw [show
          PeriodicOneInThreePositioned.formulaClauseMetadataFrom
              sourceClauseIndex (sourceClause :: rest) =
            PeriodicOneInThreePositioned.clauseMetadataFor
                sourceClauseIndex sourceClause ++
              PeriodicOneInThreePositioned.formulaClauseMetadataFrom
                (sourceClauseIndex + 1) rest by
          simp [PeriodicOneInThreePositioned.formulaClauseMetadataFrom],
        List.zipIdx_append, List.mem_append]
      rcases metadataMember with headMember | tailMember
      · left
        have valid :=
          clauseMetadataFor_valid
            sourceClauseIndex figureNineClauseStart
            sourceClause headMember
        have localMetadataMember :
            ((⟨metadata.sourceClause, metadata.sourceClauseIndex,
                figureNineClause, localClauseIndex⟩ :
                PeriodicOneInThreePositioned.ClauseMetadata Variable),
              localClauseIndex) ∈
              (PeriodicOneInThreePositioned.clauseMetadataFor
                sourceClauseIndex sourceClause).zipIdx := by
          apply List.mem_zipIdx_iff_getElem?.mpr
          simp only [PeriodicOneInThreePositioned.clauseMetadataFor,
            List.getElem?_map]
          have taggedLookup :
              (PeriodicOneInThreePositioned.clauseGadget
                sourceClauseIndex sourceClause).zipIdx[
                  localClauseIndex]? =
                some (figureNineClause, localClauseIndex) := by
            simpa [valid.1, valid.2.1] using
              (List.mem_zipIdx_iff_getElem?).mp
                figureNineClauseMember
          rw [taggedLookup]
          simp [valid.1, valid.2.1]
        simpa [valid.2.2.1] using
          mem_zipIdx_from figureNineClauseStart
            (PeriodicOneInThreePositioned.clauseMetadataFor
              sourceClauseIndex sourceClause)
            localMetadataMember
      · right
        simpa [PeriodicOneInThreePositioned.clauseMetadataFor] using
          induction
            (sourceClauseIndex := sourceClauseIndex + 1)
            (figureNineClauseStart :=
              figureNineClauseStart +
                (PeriodicOneInThreePositioned.clauseGadget
                  sourceClauseIndex sourceClause).length)
            tailMember

/-- In the complete enumeration, a metadata block's local Figure 9 indices
are therefore exact global presentation indices of the actual first-stage
positioned formula. -/
theorem formulaClauseMetadata_figureNineClause_member
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadata source)
    {figureNineClause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {localClauseIndex : Nat}
    (figureNineClauseMember :
      (figureNineClause, localClauseIndex) ∈
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex
          metadata.sourceClause).zipIdx) :
    (figureNineClause,
        metadata.figureNineClauseStart + localClauseIndex) ∈
      (PeriodicOneInThreePositioned.formula source).clauses.zipIdx := by
  have member :=
    formulaClauseMetadataFrom_figureNineClause_member
      0 0 source.clauses metadataMember figureNineClauseMember
  simpa [figureNineClausesFrom_eq_zipIdx,
    PeriodicOneInThreePositioned.formula] using member

/-- In the complete enumeration, a composed block and local Figure 9 index
also identify the exact lookup in the standard first-stage metadata list. -/
theorem formulaClauseMetadata_figureNineMetadata_lookup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadata source)
    {figureNineClause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {localClauseIndex : Nat}
    (figureNineClauseMember :
      (figureNineClause, localClauseIndex) ∈
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex
          metadata.sourceClause).zipIdx) :
    (PeriodicOneInThreePositioned.formulaClauseMetadata source)[
        metadata.figureNineClauseStart + localClauseIndex]? =
      some
        ({ sourceClause := metadata.sourceClause
           sourceClauseIndex := metadata.sourceClauseIndex
           clause := figureNineClause
           localClauseIndex := localClauseIndex } :
          PeriodicOneInThreePositioned.ClauseMetadata Variable) := by
  have member :=
    formulaClauseMetadataFrom_figureNineMetadata_member
      0 0 source.clauses metadataMember figureNineClauseMember
  simpa [PeriodicOneInThreePositioned.formulaClauseMetadataFrom_zero]
    using (List.mem_zipIdx_iff_getElem?).mp member

/-- A composed metadata entry also determines the exact local lookup in the
standard unit-elimination metadata for its source Figure 9 block. -/
theorem formulaClauseMetadata_unitEliminationMetadata_lookup_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadata source) :
    ∃ unitMetadata :
        PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata
          (OneInThreeVariable Variable),
      (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
        metadata.figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex metadata.sourceClause))[
            metadata.localClauseIndex]? =
          some unitMetadata ∧
        unitMetadata.clause = metadata.clause ∧
        (unitMetadata.sourceClause,
            unitMetadata.sourceClauseIndex) ∈
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex metadata.sourceClause).zipIdx
              metadata.figureNineClauseStart ∧
        (unitMetadata.clause, unitMetadata.localClauseIndex) ∈
          (PeriodicOneInThreeNoUnitsPositioned.clauseGadget
            unitMetadata.sourceClauseIndex
            unitMetadata.sourceClause).zipIdx := by
  have composedValid :=
    formulaClauseMetadataFrom_valid
      0 0 source.clauses metadataMember
  have localClauseLookup :
      (unitEliminationClausesFrom
        metadata.figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex metadata.sourceClause))[
            metadata.localClauseIndex]? =
        some metadata.clause :=
    (List.mem_zipIdx_iff_getElem?).mp composedValid.2
  let localMetadata :=
    PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
      metadata.figureNineClauseStart
      (PeriodicOneInThreePositioned.clauseGadget
        metadata.sourceClauseIndex metadata.sourceClause)
  have localMetadataClauses :
      localMetadata.map
          PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata.clause =
        unitEliminationClausesFrom
          metadata.figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex metadata.sourceClause) := by
    simp [localMetadata,
      PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom,
      PeriodicOneInThreeNoUnitsPositioned.clauseMetadataFor,
      unitEliminationClausesFrom_eq_zipIdx,
      List.map_flatMap, List.map_map, Function.comp_def]
  have projectedLookup :
      (localMetadata.map
        PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata.clause)[
          metadata.localClauseIndex]? =
        some metadata.clause := by
    simpa [localMetadataClauses] using localClauseLookup
  rw [List.getElem?_map, Option.map_eq_some_iff] at projectedLookup
  rcases projectedLookup with
    ⟨unitMetadata, unitMetadataLookup, unitClauseEqual⟩
  have unitMetadataMember : unitMetadata ∈ localMetadata :=
    List.mem_iff_getElem?.mpr
      ⟨metadata.localClauseIndex, unitMetadataLookup⟩
  unfold localMetadata at unitMetadataMember unitMetadataLookup
  rw [PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom,
    List.mem_flatMap] at unitMetadataMember
  rcases unitMetadataMember with
    ⟨taggedFigureNineClause, taggedFigureNineClauseMember,
      unitMetadataMember⟩
  have unitValid :=
    PeriodicOneInThreeNoUnitsPositioned.clauseMetadataFor_valid
      taggedFigureNineClause.2 taggedFigureNineClause.1
      unitMetadataMember
  refine ⟨unitMetadata, unitMetadataLookup, unitClauseEqual, ?_, ?_⟩
  · simpa [unitValid.1, unitValid.2.1] using
      taggedFigureNineClauseMember
  · simpa [unitValid.1, unitValid.2.1] using unitValid.2.2

/-- A local unit-elimination metadata lookup inside the composed source block
is the same entry at the composed clause's global index in the standard
second-stage metadata list. -/
theorem formulaClauseMetadataFrom_unitEliminationMetadata_lookup
    {Variable : Type*}
    (sourceClauseIndex figureNineClauseStart : Nat)
    (sourceClauses : List (PositionedPeriodicClause Variable))
    {metadataIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadataFrom
        sourceClauseIndex figureNineClauseStart sourceClauses)[
          metadataIndex]? = some metadata)
    {unitMetadata :
      PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata
        (OneInThreeVariable Variable)}
    (unitMetadataLookup :
      (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
        metadata.figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex metadata.sourceClause))[
            metadata.localClauseIndex]? = some unitMetadata) :
    (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
      figureNineClauseStart
      (figureNineClausesFrom
        sourceClauseIndex sourceClauses))[metadataIndex]? =
      some unitMetadata := by
  induction sourceClauses generalizing
      sourceClauseIndex figureNineClauseStart
      metadataIndex metadata with
  | nil =>
      simp [formulaClauseMetadataFrom] at metadataLookup
  | cons sourceClause rest induction =>
      let figureNineBlock :=
        PeriodicOneInThreePositioned.clauseGadget
          sourceClauseIndex sourceClause
      have composedSplit :
          formulaClauseMetadataFrom sourceClauseIndex
              figureNineClauseStart (sourceClause :: rest) =
            clauseMetadataFor sourceClauseIndex
                figureNineClauseStart sourceClause ++
              formulaClauseMetadataFrom (sourceClauseIndex + 1)
                (figureNineClauseStart + figureNineBlock.length) rest := by
        simp [formulaClauseMetadataFrom, figureNineBlock]
      have standardSplit :
          PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
              figureNineClauseStart
              (figureNineClausesFrom sourceClauseIndex
                (sourceClause :: rest)) =
            PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
                figureNineClauseStart figureNineBlock ++
              PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
                (figureNineClauseStart + figureNineBlock.length)
                (figureNineClausesFrom
                  (sourceClauseIndex + 1) rest) := by
        simp [PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom,
          figureNineClausesFrom, figureNineBlock,
          List.zipIdx_append, List.flatMap_append]
      have standardHeadClauses :
          (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
            figureNineClauseStart figureNineBlock).map
              PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata.clause =
            unitEliminationClausesFrom
              figureNineClauseStart figureNineBlock := by
        simp [PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom,
          PeriodicOneInThreeNoUnitsPositioned.clauseMetadataFor,
          unitEliminationClausesFrom_eq_zipIdx,
          List.map_flatMap, List.map_map, Function.comp_def]
      have standardHeadLength :
          (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
            figureNineClauseStart figureNineBlock).length =
            (clauseMetadataFor sourceClauseIndex
              figureNineClauseStart sourceClause).length := by
        calc
          _ = ((PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
                figureNineClauseStart figureNineBlock).map
                  PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata.clause).length := by
              simp
          _ = (unitEliminationClausesFrom
                figureNineClauseStart figureNineBlock).length := by
              rw [standardHeadClauses]
          _ = _ := by simp [clauseMetadataFor, figureNineBlock]
      rw [composedSplit] at metadataLookup
      rw [standardSplit]
      by_cases inHead :
          metadataIndex <
            (clauseMetadataFor sourceClauseIndex
              figureNineClauseStart sourceClause).length
      · rw [List.getElem?_append_left inHead] at metadataLookup
        rw [List.getElem?_append_left (by
          simpa [standardHeadLength] using inHead)]
        have metadataMember :
            metadata ∈ clauseMetadataFor sourceClauseIndex
              figureNineClauseStart sourceClause :=
          List.mem_iff_getElem?.mpr
            ⟨metadataIndex, metadataLookup⟩
        have valid :=
          clauseMetadataFor_valid sourceClauseIndex
            figureNineClauseStart sourceClause metadataMember
        have localIndexEqual :
            metadata.localClauseIndex = metadataIndex := by
          have mapped := congrArg
            (Option.map ClauseMetadata.localClauseIndex)
            metadataLookup
          simp [clauseMetadataFor] at mapped
          exact mapped.2.symm
        simpa [valid.1, valid.2.1, valid.2.2.1,
          localIndexEqual, figureNineBlock] using unitMetadataLookup
      · have headLengthLe :
            (clauseMetadataFor sourceClauseIndex
              figureNineClauseStart sourceClause).length ≤
              metadataIndex := Nat.le_of_not_gt inHead
        rw [List.getElem?_append_right headLengthLe] at metadataLookup
        rw [List.getElem?_append_right (by
          simpa [standardHeadLength] using headLengthLe)]
        simpa [standardHeadLength] using
          induction
            (sourceClauseIndex := sourceClauseIndex + 1)
            (figureNineClauseStart :=
              figureNineClauseStart + figureNineBlock.length)
            metadataLookup unitMetadataLookup

/-- Complete composed and standard second-stage metadata use the same
global final-clause index. -/
theorem formulaClauseMetadata_unitEliminationMetadata_global_lookup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clauseIndex : Nat}
    {metadata : ClauseMetadata Variable}
    (metadataLookup :
      (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    {unitMetadata :
      PeriodicOneInThreeNoUnitsPositioned.ClauseMetadata
        (OneInThreeVariable Variable)}
    (unitMetadataLookup :
      (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
        metadata.figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex metadata.sourceClause))[
            metadata.localClauseIndex]? = some unitMetadata) :
    (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadata
      (PeriodicOneInThreePositioned.formula source))[clauseIndex]? =
        some unitMetadata := by
  have lookup :=
    formulaClauseMetadataFrom_unitEliminationMetadata_lookup
      0 0 source.clauses metadataLookup unitMetadataLookup
  change
    (PeriodicOneInThreeNoUnitsPositioned.formulaClauseMetadataFrom
      0 (PeriodicOneInThreePositioned.formula source).clauses)[
        clauseIndex]? = some unitMetadata
  simpa [figureNineClausesFrom_eq_zipIdx,
    PeriodicOneInThreePositioned.formula] using lookup

/-- Every complete metadata entry has the same two membership invariants. -/
theorem formulaClauseMetadata_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadata source) :
    (metadata.sourceClause,
        metadata.sourceClauseIndex) ∈
      source.clauses.zipIdx ∧
    (metadata.clause, metadata.localClauseIndex) ∈
      (unitEliminationClausesFrom
        metadata.figureNineClauseStart
        (PeriodicOneInThreePositioned.clauseGadget
          metadata.sourceClauseIndex
          metadata.sourceClause)).zipIdx := by
  exact formulaClauseMetadataFrom_valid
    0 0 source.clauses metadataMember

/-- Every complete metadata entry also gives the corresponding embedded
clause membership in the exact formula of its certified composed drawing. -/
theorem formulaClauseMetadata_valid_embedded
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadata source) :
    (metadata.sourceClause,
        metadata.sourceClauseIndex) ∈
      source.clauses.zipIdx ∧
    (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
        metadata.localClauseIndex) ∈
      (composedClauseGadget
        metadata.sourceClauseIndex
        metadata.figureNineClauseStart
        metadata.sourceClause).zipIdx := by
  have valid :=
    formulaClauseMetadata_valid source metadataMember
  exact
    ⟨valid.1,
      localClauseMember_embedded
        metadata.sourceClauseIndex
        metadata.figureNineClauseStart
        metadata.sourceClause valid.2⟩

/-- Looking up a genuine final clause yields metadata carrying that exact
clause. -/
theorem formulaClauseMetadata_lookup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx) :
    ∃ metadata,
      (formulaClauseMetadata source)[clauseIndex]? =
        some metadata ∧
      metadata.clause = clause := by
  have clauseLookup :
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses[
          clauseIndex]? =
        some clause :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have projectedLookup :
      ((formulaClauseMetadata source).map
          ClauseMetadata.clause)[clauseIndex]? =
        some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simpa only [Option.map_eq_some_iff] using projectedLookup

/-- A genuine final lookup also returns the original-source and local-block
membership invariants needed to select its certified composed route. -/
theorem formulaClauseMetadata_lookup_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx) :
    ∃ metadata,
      (formulaClauseMetadata source)[clauseIndex]? =
        some metadata ∧
      metadata.clause = clause ∧
      (metadata.sourceClause,
          metadata.sourceClauseIndex) ∈
        source.clauses.zipIdx ∧
      (metadata.clause, metadata.localClauseIndex) ∈
        (unitEliminationClausesFrom
          metadata.figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex
            metadata.sourceClause)).zipIdx := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have metadataIndexLt :
      clauseIndex <
        (formulaClauseMetadata source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (formulaClauseMetadata source)[clauseIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈ formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  exact
    ⟨metadata, metadataLookup, clauseEqual,
      formulaClauseMetadata_valid
        source metadataMember⟩

/-- A genuine final lookup additionally identifies its exact clause
occurrence in the embedded composed drawing formula. -/
theorem formulaClauseMetadata_lookup_valid_embedded
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx) :
    ∃ metadata,
      (formulaClauseMetadata source)[clauseIndex]? =
        some metadata ∧
      metadata.clause = clause ∧
      (metadata.sourceClause,
          metadata.sourceClauseIndex) ∈
        source.clauses.zipIdx ∧
      (PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
          metadata.localClauseIndex) ∈
        (composedClauseGadget
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).zipIdx := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have metadataIndexLt :
      clauseIndex <
        (formulaClauseMetadata source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (formulaClauseMetadata source)[clauseIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈ formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  exact
    ⟨metadata, metadataLookup, clauseEqual,
      formulaClauseMetadata_valid_embedded
        source metadataMember⟩

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
