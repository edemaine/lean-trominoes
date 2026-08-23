/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransition
import LeanTrominoes.PeriodicCNFZeroAnchorData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceData

/-! # Horizontal offsets of copied occurrence incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- In a zero-anchored forward-local presentation, every copied occurrence
incidence stays in the current slice or points to the next slice. -/
theorem occurrenceIncidences_edge_offset_zero_or_one
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (forward : source.IsForwardLocal)
    (zeroAnchored : source.IsZeroAnchored) :
    ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0) := by
  intro copied copiedMember
  rcases List.mem_map.mp copiedMember with
    ⟨incidence, incidenceMember, rfl⟩
  have members :=
    (PeriodicCNF.mem_incidencesWithMetadata_iff source incidence).mp
      incidenceMember
  have clauseMember : incidence.clause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx members.1
  have literalMember : incidence.literal ∈ incidence.clause :=
    List.fst_mem_of_mem_zipIdx members.2
  have literalForward :=
    forward incidence.clause clauseMember incidence.literal literalMember
  have anchorZero :
      PeriodicCNF.clauseAnchor incidence.clause = (0, 0) :=
    zeroAnchored incidence.clause clauseMember
  have copiedOffset :
      (occurrenceIncidence incidence).edge.offset =
        incidence.literal.offset := by
    change Cell.sub
      (occurrenceIncidence incidence).literal.offset
      (PeriodicCNF.clauseAnchor
        (occurrenceIncidence incidence).clause) = incidence.literal.offset
    rw [occurrenceIncidence_literal_offset, occurrenceIncidence_clause,
      clauseAnchor_occurrenceClause, anchorZero]
    simp [Cell.sub]
  rw [copiedOffset]
  exact literalForward

end PeriodicThreeSATThree
end LeanTrominoes
