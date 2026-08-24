/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupSemantics

/-! # Unary lookup through support-guarded representative rows -/

namespace LeanTrominoes

namespace LastTrueUnaryValueLookupMachine

variable {Value : Type*} [DecidableEq Value]

/-- An equality row selects the datum attached to its value when the aligned
datum stream is obtained by mapping one function over the value stream. -/
theorem lookup_equalityRow_map (datum : Value → Nat)
    (values : List Value) (target : Value) (targetMem : target ∈ values) :
    lookup (StableOccurrenceRanks.equalityRow values target)
        (values.map datum) =
      datum target := by
  unfold lookup
  induction values with
  | nil => simp at targetMem
  | cons value values induction =>
      by_cases same : target = value
      · subst value
        by_cases later : target ∈ values
        · have irrelevant :=
            lookupAux_equalityRow_candidate_irrelevant
              (datum target) 0 target values (values.map datum) later
          simpa [StableOccurrenceRanks.equalityRow, lookupAux] using
              (irrelevant.trans (induction later))
        · have unchanged :=
            lookupAux_equalityRow_of_not_mem
              (datum target) target values (values.map datum) later
          simpa [StableOccurrenceRanks.equalityRow, lookupAux] using unchanged
      · have later : target ∈ values := by
          simpa [same] using targetMem
        simpa [StableOccurrenceRanks.equalityRow,
          lookupAux, same] using induction later

end LastTrueUnaryValueLookupMachine

end LeanTrominoes
