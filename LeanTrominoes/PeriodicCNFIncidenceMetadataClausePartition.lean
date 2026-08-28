/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataAppend

/-! # Clause partition of globally indexed incidence metadata -/

namespace LeanTrominoes
namespace PeriodicCNF

private theorem start_le_snd_of_mem_zipIdx
    {Value : Type*} (values : List Value) (start : Nat)
    (tagged : Value × Nat) (member : tagged ∈ values.zipIdx start) :
    start ≤ tagged.2 := by
  induction values generalizing start with
  | nil => simp at member
  | cons value values induction =>
      rw [List.zipIdx_cons] at member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        omega
      · have lower := induction (start + 1) member
        omega

private theorem incidenceMetadataBlock_clauseIndex
    {Variable : Type*}
    (taggedClause : PeriodicClause Variable × Nat)
    {incidence : CNFIncidence Variable}
    (member : incidence ∈ incidenceMetadataBlock taggedClause) :
    incidence.clauseIndex = taggedClause.2 := by
  unfold incidenceMetadataBlock at member
  rcases List.mem_map.mp member with
    ⟨taggedLiteral, _taggedLiteralMember, rfl⟩
  rfl

private theorem filter_zipIdx_incidenceMetadataBlock_same
    {Variable : Type*}
    (taggedClause : PeriodicClause Variable × Nat)
    (start : Nat) :
    ((incidenceMetadataBlock taggedClause).zipIdx start).filter
        (fun tagged =>
          decide (tagged.1.clauseIndex = taggedClause.2)) =
      (incidenceMetadataBlock taggedClause).zipIdx start := by
  apply List.filter_eq_self.mpr
  intro tagged taggedMember
  have incidenceMember := List.fst_mem_of_mem_zipIdx taggedMember
  exact decide_eq_true
    (incidenceMetadataBlock_clauseIndex taggedClause incidenceMember)

private theorem filter_zipIdx_incidenceMetadataBlock_ne
    {Variable : Type*}
    (taggedClause : PeriodicClause Variable × Nat)
    (start selected : Nat)
    (different : taggedClause.2 ≠ selected) :
    ((incidenceMetadataBlock taggedClause).zipIdx start).filter
        (fun tagged => decide (tagged.1.clauseIndex = selected)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro tagged taggedMember
  have incidenceMember := List.fst_mem_of_mem_zipIdx taggedMember
  have indexEq :=
    incidenceMetadataBlock_clauseIndex taggedClause incidenceMember
  simp [indexEq, different]

private theorem filter_zipIdx_incidenceMetadataBlocksFrom_before
    {Variable : Type*}
    (clauses : List (PeriodicClause Variable))
    (clauseStart incidenceStart selected : Nat)
    (before : selected < clauseStart) :
    ((incidenceMetadataBlocksFrom clauseStart clauses).zipIdx
        incidenceStart).filter
        (fun tagged => decide (tagged.1.clauseIndex = selected)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro tagged taggedMember
  have incidenceMember := List.fst_mem_of_mem_zipIdx taggedMember
  unfold incidenceMetadataBlocksFrom at incidenceMember
  rcases List.mem_flatMap.mp incidenceMember with
    ⟨taggedClause, taggedClauseMember, incidenceMember⟩
  have clauseLower := start_le_snd_of_mem_zipIdx
    clauses clauseStart taggedClause taggedClauseMember
  have indexEq :=
    incidenceMetadataBlock_clauseIndex taggedClause incidenceMember
  have different : tagged.1.clauseIndex ≠ selected := by
    rw [indexEq]
    omega
  simp [different]

private theorem clausePartitionFrom
    {Variable : Type*}
    (clauses : List (PeriodicClause Variable))
    (clauseStart incidenceStart : Nat) :
    ((clauses.zipIdx clauseStart).flatMap fun taggedClause =>
        ((incidenceMetadataBlocksFrom clauseStart clauses).zipIdx
          incidenceStart).filter fun taggedIncidence =>
            decide
              (taggedIncidence.1.clauseIndex = taggedClause.2)) =
      (incidenceMetadataBlocksFrom clauseStart clauses).zipIdx
        incidenceStart := by
  induction clauses generalizing clauseStart incidenceStart with
  | nil => rfl
  | cons clause clauses induction =>
      let head : PeriodicClause Variable × Nat := (clause, clauseStart)
      let headBlock := incidenceMetadataBlock head
      let tailBlocks := incidenceMetadataBlocksFrom
        (clauseStart + 1) clauses
      have blocksEq :
          incidenceMetadataBlocksFrom clauseStart (clause :: clauses) =
            headBlock ++ tailBlocks := by
        rfl
      rw [blocksEq, List.zipIdx_append, List.zipIdx_cons,
        List.flatMap_cons]
      rw [List.filter_append,
        filter_zipIdx_incidenceMetadataBlock_same]
      rw [filter_zipIdx_incidenceMetadataBlocksFrom_before
        clauses (clauseStart + 1)
        (incidenceStart + headBlock.length) clauseStart (by omega)]
      simp only [List.append_nil]
      apply congrArg₂ List.append rfl
      calc
        (clauses.zipIdx (clauseStart + 1)).flatMap
            (fun taggedClause =>
              ((headBlock.zipIdx incidenceStart ++
                  tailBlocks.zipIdx
                    (incidenceStart + headBlock.length)).filter
                fun taggedIncidence =>
                  decide
                    (taggedIncidence.1.clauseIndex = taggedClause.2))) =
            (clauses.zipIdx (clauseStart + 1)).flatMap
              (fun taggedClause =>
                (tailBlocks.zipIdx
                  (incidenceStart + headBlock.length)).filter
                    fun taggedIncidence =>
                      decide
                        (taggedIncidence.1.clauseIndex =
                          taggedClause.2)) := by
          apply List.flatMap_congr
          intro taggedClause taggedClauseMember
          rw [List.filter_append]
          have lower := start_le_snd_of_mem_zipIdx clauses
            (clauseStart + 1) taggedClause taggedClauseMember
          rw [filter_zipIdx_incidenceMetadataBlock_ne
            head incidenceStart taggedClause.2 (by
              unfold head
              omega)]
          rfl
        _ = tailBlocks.zipIdx
              (incidenceStart + headBlock.length) := by
          exact induction (clauseStart + 1)
            (incidenceStart + headBlock.length)

/-- Clause-major filtering of the globally indexed incidence stream is an
exact ordered partition, not merely a permutation. -/
theorem clauses_flatMap_filter_incidencesWithMetadata_zipIdx
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    (formula.clauses.zipIdx.flatMap fun taggedClause =>
        formula.incidencesWithMetadata.zipIdx.filter
          (fun taggedIncidence =>
            decide
              (taggedIncidence.1.clauseIndex = taggedClause.2))) =
      formula.incidencesWithMetadata.zipIdx := by
  change
    ((formula.clauses.zipIdx 0).flatMap fun taggedClause =>
        ((incidenceMetadataBlocksFrom 0 formula.clauses).zipIdx 0).filter
          (fun taggedIncidence =>
            decide
              (taggedIncidence.1.clauseIndex = taggedClause.2))) =
      (incidenceMetadataBlocksFrom 0 formula.clauses).zipIdx 0
  exact clausePartitionFrom formula.clauses 0 0

end PeriodicCNF
end LeanTrominoes
