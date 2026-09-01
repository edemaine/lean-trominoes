/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanDataTripleAssembler

/-! # Count-predecessor projection of assembled fan triples -/

noncomputable section

namespace LeanTrominoes.FinalFanDataTripleAssembler

def repeatedCountPreds (countPreds : List (Fin 3)) : List (Fin 3) :=
  countPreds.flatMap fun countPred => List.replicate 3 countPred

def countedOccurrencePairs
    (data : List OccurrenceData) (countPreds : List (Fin 3)) : List Pair :=
  (List.zipWith Prod.mk data (repeatedCountPreds countPreds)).map fun pair =>
    (pair.1, slotOfCountPred pair.2)

@[simp] theorem repeatedCountPreds_length (countPreds : List (Fin 3)) :
    (repeatedCountPreds countPreds).length = 3 * countPreds.length := by
  simp [repeatedCountPreds, Nat.mul_comm]

/-- Grouping a stream whose count predecessor is repeated on each
consecutive triple recovers exactly the original count-predecessor column. -/
theorem output_countPreds_countedOccurrencePairs
    (countPreds : List (Fin 3)) (data : List OccurrenceData)
    (lengthEq : data.length = 3 * countPreds.length) :
    (output (countedOccurrencePairs data countPreds)).map
        (fun fan => fan.countPred) = countPreds := by
  induction countPreds generalizing data with
  | nil =>
      have dataNil : data = [] := List.eq_nil_of_length_eq_zero lengthEq
      subst data
      rfl
  | cons countPred countPreds induction =>
      cases data with
      | nil => simp at lengthEq
      | cons first data =>
          cases data with
          | nil =>
              simp only [List.length_cons, List.length_nil] at lengthEq
              omega
          | cons second data =>
              cases data with
              | nil =>
                  simp only [List.length_cons, List.length_nil] at lengthEq
                  omega
              | cons third remaining =>
                  have tailLength :
                      remaining.length = 3 * countPreds.length := by
                    simp only [List.length_cons] at lengthEq
                    omega
                  rw [show countedOccurrencePairs
                      (first :: second :: third :: remaining)
                      (countPred :: countPreds) =
                    (first, slotOfCountPred countPred) ::
                      (second, slotOfCountPred countPred) ::
                      (third, slotOfCountPred countPred) ::
                      countedOccurrencePairs remaining countPreds by
                    rfl]
                  rw [output_eq_grouped]
                  simp only [grouped, List.map_cons, fanData_countPred,
                    countPredOfSlot_slotOfCountPred]
                  rw [← output_eq_grouped,
                    induction remaining tailLength]

end LeanTrominoes.FinalFanDataTripleAssembler

end
