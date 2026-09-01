/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.UnaryKeyedValueLookupUniqueSemantics

/-! # Projecting finite keyed lookup data -/

namespace LeanTrominoes.FiniteAlphabetKeyedValueLookup

variable {Value Target : Type} [Inhabited Value] [Inhabited Target]

/-- Projecting a finite datum selected at a present unique key is the same
as selecting from the projected candidate column. -/
theorem map_alignedDatum_projection
    (queries candidateKeys : List Nat) (candidateValues : List Value)
    (project : Value → Target)
    (aligned : candidateKeys.length = candidateValues.length)
    (present : ∀ query ∈ queries, query ∈ candidateKeys) :
    (queries.map (alignedDatum candidateKeys candidateValues)).map project =
      queries.map
        (FiniteAlphabetKeyedValueLookup.alignedDatum candidateKeys
          (candidateValues.map project)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro query queryMember
  have indexLt : candidateKeys.idxOf query < candidateKeys.length :=
    List.idxOf_lt_length_iff.mpr (present query queryMember)
  have valueIndexLt : candidateKeys.idxOf query < candidateValues.length := by
    simpa [← aligned] using indexLt
  unfold alignedDatum
  change
    project (candidateValues.getD (candidateKeys.idxOf query) default) =
      (candidateValues.map project).getD
        (candidateKeys.idxOf query) default
  rw [List.getD_eq_getElem _ _ valueIndexLt,
    List.getD_eq_getElem _ _ (by simpa using valueIndexLt),
    List.getElem_map]

end LeanTrominoes.FiniteAlphabetKeyedValueLookup
