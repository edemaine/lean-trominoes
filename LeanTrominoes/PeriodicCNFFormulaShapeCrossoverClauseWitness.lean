/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedBlockDistinctness
import LeanTrominoes.PeriodicOrthocrossingSegments

/-! # Canonical witnesses for normalized crossover clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A canonical crossing key and local fixed clause whose wrapped normalized
literal list is the specified clause. -/
structure CrossoverClauseWitness
    {Variable : Type}
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)) where
  crossing : CrossingRecord
  taggedClause : EmbeddedClause CrossoverVariable × Nat
  taggedClauseMember : taggedClause ∈ crossoverFormula.zipIdx
  clauseEqual :
    FormulaShapeCrossoverDirection.wrappedNormalizedClause
      crossing taggedClause.1 = clause

/-- Mapping one fixed tagged clause into a canonical block preserves its
local `zipIdx` index. -/
theorem wrappedNormalizedClause_mem_canonicalBlock_zipIdx
    {Variable : Type}
    (crossing : CrossingRecord)
    (taggedClause : EmbeddedClause CrossoverVariable × Nat)
    (taggedClauseMember : taggedClause ∈ crossoverFormula.zipIdx) :
    (FormulaShapeCrossoverDirection.wrappedNormalizedClause
        (Variable := Variable) crossing taggedClause.1,
      taggedClause.2) ∈
      (canonicalNormalizedCrossoverBlock
        (Variable := Variable) crossing).zipIdx := by
  unfold canonicalNormalizedCrossoverBlock
  rw [List.zipIdx_map]
  apply List.mem_map.mpr
  refine ⟨(taggedClause, taggedClause.2), ?_, rfl⟩
  apply (List.mem_zipIdx_iff_getElem?).mpr
  rw [List.getElem?_zipIdx]
  simpa using congrArg (fun value => value.map fun clause =>
      (clause, taggedClause.2))
      ((List.mem_zipIdx_iff_getElem?).mp taggedClauseMember)

/-- The canonical crossing key and local fixed clause of a normalized
crossover clause are unique. -/
theorem CrossoverClauseWitness.unique
    {Variable : Type} [DecidableEq Variable]
    {clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)}
    (first second : CrossoverClauseWitness clause) :
    first.crossing = second.crossing ∧
      first.taggedClause = second.taggedClause := by
  have firstBlockMember :
      clause ∈ canonicalNormalizedCrossoverBlock
        (Variable := Variable) first.crossing :=
    List.mem_map.mpr
      ⟨first.taggedClause, first.taggedClauseMember,
        first.clauseEqual⟩
  have secondBlockMember :
      clause ∈ canonicalNormalizedCrossoverBlock
        (Variable := Variable) second.crossing :=
    List.mem_map.mpr
      ⟨second.taggedClause, second.taggedClauseMember,
        second.clauseEqual⟩
  have crossingEqual : first.crossing = second.crossing := by
    by_contra different
    exact (canonicalNormalizedCrossoverBlock_disjoint
      (Variable := Variable) different)
        firstBlockMember secondBlockMember
  have firstIndexedMember :
      (clause, first.taggedClause.2) ∈
        (canonicalNormalizedCrossoverBlock
          (Variable := Variable) first.crossing).zipIdx := by
    have member :=
      wrappedNormalizedClause_mem_canonicalBlock_zipIdx
        (Variable := Variable) first.crossing
        first.taggedClause first.taggedClauseMember
    rwa [first.clauseEqual] at member
  have secondIndexedMember :
      (clause, second.taggedClause.2) ∈
        (canonicalNormalizedCrossoverBlock
          (Variable := Variable) first.crossing).zipIdx := by
    have member :=
      wrappedNormalizedClause_mem_canonicalBlock_zipIdx
        (Variable := Variable) second.crossing
        second.taggedClause second.taggedClauseMember
    rw [second.clauseEqual] at member
    simpa [crossingEqual] using member
  have firstIndex :=
    IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
      (canonicalNormalizedCrossoverBlock
        (Variable := Variable) first.crossing)
      (canonicalNormalizedCrossoverBlock_nodup first.crossing)
      (clause, first.taggedClause.2) firstIndexedMember
  have secondIndex :=
    IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
      (canonicalNormalizedCrossoverBlock
        (Variable := Variable) first.crossing)
      (canonicalNormalizedCrossoverBlock_nodup first.crossing)
      (clause, second.taggedClause.2) secondIndexedMember
  have localIndexEqual :
      first.taggedClause.2 = second.taggedClause.2 :=
    firstIndex.symm.trans secondIndex
  exact ⟨crossingEqual,
    tagged_eq_of_mem_zipIdx_of_snd_eq
      first.taggedClauseMember second.taggedClauseMember
      localIndexEqual⟩

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
