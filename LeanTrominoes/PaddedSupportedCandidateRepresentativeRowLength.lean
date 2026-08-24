/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowData

/-! # Lengths of guarded candidate representative rows -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

variable {Value : Type*}

/-- Every sentinel-free representative row remains a full row of the
sentinel-completed guarded-word square. -/
theorem representativeRows_forall_length
    (encodeValue : Value → List Bool)
    (candidates : List
      (PaddedSupportedLastRepresentativeEqualityRows.Candidate Value)) :
    (representativeRows encodeValue candidates).words.Forall fun row =>
      row.length = candidates.length + 1 := by
  unfold representativeRows representativeRowsWithSentinel
    equalityRowsWithSentinel
  rw [LastRepresentativeEqualityRows.rows_equalityRows]
  rw [List.forall_iff_forall_mem]
  intro row rowMember
  have rowMember' := List.dropLast_subset _ rowMember
  rcases List.mem_map.mp rowMember' with ⟨word, _, rfl⟩
  simp [LastRepresentativeEqualityRows.equalityRow]

end LeanTrominoes.PaddedSupportedCandidateWords
