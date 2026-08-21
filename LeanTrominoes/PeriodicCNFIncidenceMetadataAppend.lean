/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataLocalRanks

/-! # Appending CNF incidence metadata streams -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Metadata blocks for an explicit clause list whose clause indices start at
an arbitrary offset. -/
def incidenceMetadataBlocksFrom {Variable : Type*}
    (start : Nat) (clauses : List (PeriodicClause Variable)) :
    List (CNFIncidence Variable) :=
  (clauses.zipIdx start).flatMap incidenceMetadataBlock

@[simp] theorem incidenceMetadataBlocksFrom_zero
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    incidenceMetadataBlocksFrom 0 formula.clauses =
      incidencesWithMetadata formula := by
  exact (incidencesWithMetadata_eq_blocks formula).symm

/-- Appending clauses concatenates their metadata blocks while shifting only
the second block's clause indices. -/
theorem incidenceMetadataBlocksFrom_append
    {Variable : Type*} (start : Nat)
    (first second : List (PeriodicClause Variable)) :
    incidenceMetadataBlocksFrom start (first ++ second) =
      incidenceMetadataBlocksFrom start first ++
        incidenceMetadataBlocksFrom (start + first.length) second := by
  unfold incidenceMetadataBlocksFrom
  rw [List.zipIdx_append, List.flatMap_append]

/-- Formula metadata for an appended clause presentation has the unshifted
first formula's metadata as an exact prefix. -/
theorem incidencesWithMetadata_append
    {Variable : Type*}
    (first second : List (PeriodicClause Variable)) :
    incidencesWithMetadata (PeriodicCNF.mk (first ++ second)) =
      incidencesWithMetadata (PeriodicCNF.mk first) ++
        incidenceMetadataBlocksFrom first.length second := by
  change incidenceMetadataBlocksFrom 0 (first ++ second) = _
  rw [incidenceMetadataBlocksFrom_append]
  rw [Nat.zero_add]
  exact congrArg
    (fun metadataPrefix => metadataPrefix ++
      incidenceMetadataBlocksFrom first.length second)
    (incidenceMetadataBlocksFrom_zero (PeriodicCNF.mk first))

/-- Taking the size of the first metadata stream from an appended formula
recovers that stream exactly. -/
theorem incidencesWithMetadata_append_take_prefix
    {Variable : Type*}
    (first second : List (PeriodicClause Variable)) :
    (incidencesWithMetadata (PeriodicCNF.mk (first ++ second))).take
        (incidencesWithMetadata (PeriodicCNF.mk first)).length =
      incidencesWithMetadata (PeriodicCNF.mk first) := by
  rw [incidencesWithMetadata_append]
  simp

end PeriodicCNF
end LeanTrominoes
