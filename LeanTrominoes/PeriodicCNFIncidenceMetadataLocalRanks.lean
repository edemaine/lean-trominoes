/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicCNFIncidenceMetadataOccurrences
import LeanTrominoes.PeriodicOrthocrossingPortRankPrefix

/-! # Literal-local ranks in the flattened CNF incidence stream -/

namespace LeanTrominoes

namespace PeriodicCNF

/-- The metadata block contributed by one indexed clause. -/
def incidenceMetadataBlock {Variable : Type*}
    (taggedClause : PeriodicClause Variable × Nat) :
    List (CNFIncidence Variable) :=
  taggedClause.1.zipIdx.map fun taggedLiteral =>
    ⟨taggedClause.2, taggedClause.1,
      taggedLiteral.2, taggedLiteral.1⟩

@[simp] theorem incidenceMetadataBlock_length
    {Variable : Type*}
    (taggedClause : PeriodicClause Variable × Nat) :
    (incidenceMetadataBlock taggedClause).length =
      taggedClause.1.length := by
  simp [incidenceMetadataBlock]

theorem incidencesWithMetadata_eq_blocks
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    incidencesWithMetadata formula =
      formula.clauses.zipIdx.flatMap incidenceMetadataBlock := by
  rfl

private theorem filter_incidenceMetadataBlock_eq_self
    {Variable : Type*}
    (taggedClause : PeriodicClause Variable × Nat) :
    (incidenceMetadataBlock taggedClause).filter
        (fun incidence =>
          decide (incidence.clauseIndex = taggedClause.2)) =
      incidenceMetadataBlock taggedClause := by
  unfold incidenceMetadataBlock
  generalize taggedClause.1.zipIdx = taggedLiterals
  induction taggedLiterals with
  | nil => rfl
  | cons taggedLiteral taggedLiterals induction =>
      simp [induction]

private theorem filter_incidenceMetadataBlock_eq_nil
    {Variable : Type*}
    (taggedClause : PeriodicClause Variable × Nat) (clauseIndex : Nat)
    (different : taggedClause.2 ≠ clauseIndex) :
    (incidenceMetadataBlock taggedClause).filter
        (fun incidence => decide (incidence.clauseIndex = clauseIndex)) =
      [] := by
  unfold incidenceMetadataBlock
  generalize taggedClause.1.zipIdx = taggedLiterals
  induction taggedLiterals with
  | nil => rfl
  | cons taggedLiteral taggedLiterals induction =>
      simp [different, induction]

private theorem filter_blocks_eq_nil_of_index_not_mem
    {Variable : Type*}
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (clauseIndex : Nat)
    (notMember : clauseIndex ∉ taggedClauses.map Prod.snd) :
    (taggedClauses.flatMap incidenceMetadataBlock).filter
        (fun incidence => decide (incidence.clauseIndex = clauseIndex)) =
      [] := by
  induction taggedClauses with
  | nil => rfl
  | cons taggedClause taggedClauses induction =>
      have headDifferent : taggedClause.2 ≠ clauseIndex := by
        intro equal
        apply notMember
        simp [equal]
      have tailNotMember :
          clauseIndex ∉ taggedClauses.map Prod.snd := by
        intro member
        apply notMember
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr member
      simp only [List.flatMap_cons, List.filter_append]
      rw [filter_incidenceMetadataBlock_eq_nil
          taggedClause clauseIndex headDifferent,
        induction tailNotMember]
      rfl

private theorem filter_blocks_eq_member
    {Variable : Type*}
    (taggedClauses : List (PeriodicClause Variable × Nat))
    (indicesNodup : (taggedClauses.map Prod.snd).Nodup)
    (target : PeriodicClause Variable × Nat)
    (targetMember : target ∈ taggedClauses) :
    (taggedClauses.flatMap incidenceMetadataBlock).filter
        (fun incidence =>
          decide (incidence.clauseIndex = target.2)) =
      incidenceMetadataBlock target := by
  induction taggedClauses with
  | nil => simp at targetMember
  | cons taggedClause taggedClauses induction =>
      have headNotTail : taggedClause.2 ∉ taggedClauses.map Prod.snd :=
        (List.nodup_cons.mp indicesNodup).1
      have tailNodup : (taggedClauses.map Prod.snd).Nodup :=
        (List.nodup_cons.mp indicesNodup).2
      rcases List.mem_cons.mp targetMember with targetEq | targetMember
      · subst target
        simp only [List.flatMap_cons, List.filter_append]
        rw [filter_incidenceMetadataBlock_eq_self,
          filter_blocks_eq_nil_of_index_not_mem
            taggedClauses taggedClause.2 headNotTail,
          List.append_nil]
      · have headDifferent : taggedClause.2 ≠ target.2 := by
          intro equal
          exact headNotTail (List.mem_map.mpr
            ⟨target, targetMember, equal.symm⟩)
        simp only [List.flatMap_cons, List.filter_append]
        rw [filter_incidenceMetadataBlock_eq_nil
            taggedClause target.2 headDifferent,
          induction tailNodup targetMember,
          List.nil_append]

/-- Selecting the flattened incidence stream by a genuine clause index
recovers exactly that clause's metadata block. -/
theorem incidencesWithMetadata_filter_clauseIndex
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    (taggedClause : PeriodicClause Variable × Nat)
    (taggedClauseMember : taggedClause ∈ formula.clauses.zipIdx) :
    (incidencesWithMetadata formula).filter
        (fun incidence =>
          decide (incidence.clauseIndex = taggedClause.2)) =
      incidenceMetadataBlock taggedClause := by
  rw [incidencesWithMetadata_eq_blocks]
  exact filter_blocks_eq_member formula.clauses.zipIdx
    (List.nodup_zipIdx_map_snd formula.clauses)
    taggedClause taggedClauseMember

end PeriodicCNF

namespace List

private theorem count_map_eq_filter_length
    {α β : Type*} [DecidableEq β]
    (values : List α) (field : α → β) (target : β) :
    (values.map field).count target =
      (values.filter fun value => decide (field value = target)).length := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      by_cases same : field value = target <;> simp [same, induction]

end List

namespace PeriodicCNF

/-- In clause-major metadata order, the number of prior incidences from the
same clause is exactly the literal's within-clause presentation index. -/
theorem metadataIncidence_priorClauseCount_eq_literalIndex
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember : tagged ∈ (incidencesWithMetadata formula).zipIdx) :
    (((incidencesWithMetadata formula).take tagged.2).map
        CNFIncidence.clauseIndex).count tagged.1.clauseIndex =
      tagged.1.literalIndex := by
  let stream := incidencesWithMetadata formula
  have incidenceMember : tagged.1 ∈ stream :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have indexEq : stream.idxOf tagged.1 = tagged.2 :=
      by
    have indexLt : tagged.2 < stream.length :=
      List.snd_lt_of_mem_zipIdx taggedMember
    have valueEq : stream[tagged.2] = tagged.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp taggedMember)).2
    rw [← valueEq]
    exact (incidencesWithMetadata_nodup formula).idxOf_getElem
      tagged.2 indexLt
  have selected :
      decide (tagged.1.clauseIndex = tagged.1.clauseIndex) = true := by
    simp
  have filteredIndex :=
    List.idxOf_filter_eq_filter_take_idxOf_length
      (fun incidence : CNFIncidence Variable =>
        decide (incidence.clauseIndex = tagged.1.clauseIndex))
      stream tagged.1 incidenceMember selected
  have members :=
    (mem_incidencesWithMetadata_iff formula tagged.1).mp incidenceMember
  have filteredStream :
      stream.filter (fun incidence =>
        decide (incidence.clauseIndex = tagged.1.clauseIndex)) =
        incidenceMetadataBlock
          (tagged.1.clause, tagged.1.clauseIndex) := by
    exact incidencesWithMetadata_filter_clauseIndex formula
      (tagged.1.clause, tagged.1.clauseIndex) members.1
  have blockNodup :
      (incidenceMetadataBlock
        (tagged.1.clause, tagged.1.clauseIndex)).Nodup := by
    rw [← filteredStream]
    exact (incidencesWithMetadata_nodup formula).filter _
  have blockTaggedMember :
      (tagged.1, tagged.1.literalIndex) ∈
        (incidenceMetadataBlock
          (tagged.1.clause, tagged.1.clauseIndex)).zipIdx := by
    apply (List.mem_zipIdx_iff_getElem?).mpr
    unfold incidenceMetadataBlock
    rw [List.getElem?_map, List.getElem?_zipIdx]
    have literalLookup :=
      (List.mem_zipIdx_iff_getElem?).mp members.2
    rw [literalLookup]
    cases tagged.1
    simp
  have blockIndex :
      (incidenceMetadataBlock
        (tagged.1.clause, tagged.1.clauseIndex)).idxOf tagged.1 =
          tagged.1.literalIndex :=
      by
    have indexLt : tagged.1.literalIndex <
        (incidenceMetadataBlock
          (tagged.1.clause, tagged.1.clauseIndex)).length :=
      List.snd_lt_of_mem_zipIdx blockTaggedMember
    have valueEq :
        (incidenceMetadataBlock
          (tagged.1.clause, tagged.1.clauseIndex))[tagged.1.literalIndex] =
            tagged.1 :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp blockTaggedMember)).2
    calc
      (incidenceMetadataBlock
          (tagged.1.clause, tagged.1.clauseIndex)).idxOf tagged.1 =
          (incidenceMetadataBlock
            (tagged.1.clause, tagged.1.clauseIndex)).idxOf
              (incidenceMetadataBlock
                (tagged.1.clause,
                  tagged.1.clauseIndex))[tagged.1.literalIndex] :=
        congrArg
          (fun incidence =>
            (incidenceMetadataBlock
              (tagged.1.clause,
                tagged.1.clauseIndex)).idxOf incidence)
          valueEq.symm
      _ = tagged.1.literalIndex :=
        blockNodup.idxOf_getElem tagged.1.literalIndex indexLt
  rw [← indexEq]
  rw [List.count_map_eq_filter_length]
  rw [← filteredIndex, filteredStream, blockIndex]

end PeriodicCNF
end LeanTrominoes
