/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockIndexCompiler

/-! # Looking up values at finite block indices -/

namespace LeanTrominoes.FiniteBlockIndices

/-- Pair each source item with its aligned value and repeat that value across
the item's complete output block. -/
def broadcastValues {Source Value : Type*}
  (blockLength : Source → Nat) (source : List Source)
    (values : List Value) : List Value :=
  (List.zipWith
    (fun item value => List.replicate (blockLength item) value)
    source values).flatten

private theorem expectedAux_lookup_eq_broadcastValues
    {Source Value : Type*} (blockLength : Source → Nat)
    (default : Value) (earlier : List Value)
    (source : List Source) (values : List Value)
    (lengthEq : source.length = values.length)
    (positive : ∀ item ∈ source, 0 < blockLength item) :
    (expectedAux blockLength earlier.length source).map
        (fun index => (earlier ++ values).getD index default) =
      broadcastValues blockLength source values := by
  induction source generalizing earlier values with
  | nil =>
      have valuesEmpty : values = [] :=
        List.length_eq_zero_iff.mp lengthEq.symm
      subst values
      rfl
  | cons item source induction =>
      cases values with
      | nil => simp at lengthEq
      | cons value values =>
          have tailLength : source.length = values.length := by
            simpa using lengthEq
          have itemPositive : 0 < blockLength item :=
            positive item (by simp)
          have tailPositive : ∀ later ∈ source,
              0 < blockLength later := by
            intro later laterMember
            exact positive later (by simp [laterMember])
          have tail := induction (earlier := earlier ++ [value])
            (values := values) tailLength tailPositive
          have boundaryLt : earlier.length <
              (earlier ++ value :: values).length := by simp
          have boundaryValue :
              (earlier ++ value :: values).getD earlier.length default =
                value := by
            rw [List.getD_eq_getElem _ _ boundaryLt]
            simp
          simp only [expectedAux, List.map_append, List.map_replicate,
            nextIndex, Nat.ne_of_gt itemPositive, if_false,
            broadcastValues, List.zipWith_cons_cons, List.flatten_cons]
          rw [boundaryValue]
          rw [show earlier.length + 1 = (earlier ++ [value]).length by simp]
          simpa [broadcastValues, List.append_assoc] using tail

/-- With one nonempty block per source item, looking up the compiled block
indices broadcasts each aligned value over exactly that item's block. -/
theorem expected_lookup_eq_broadcastValues
    {Source Value : Type*} (blockLength : Source → Nat)
    (source : List Source) (values : List Value) (default : Value)
    (lengthEq : source.length = values.length)
    (positive : ∀ item ∈ source, 0 < blockLength item) :
    (expected blockLength source).map
        (fun index => values.getD index default) =
      broadcastValues blockLength source values := by
  simpa [expected] using
    expectedAux_lookup_eq_broadcastValues blockLength default []
      source values lengthEq positive

end LeanTrominoes.FiniteBlockIndices
