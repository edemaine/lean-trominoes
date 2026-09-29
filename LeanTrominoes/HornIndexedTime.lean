/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.HornIndexedSolver
import LeanTrominoes.HornIndexedPreparation
import LeanTrominoes.HornWorklistRAM

/-! # Complete indexed-RAM bound, including premise indexing

The input explicitly has `n` variable slots, a rule array, and linked premise
lists. Variable names are already slot indices, as recorded in the input type.
The bound includes traversal of that input to create numbered occurrences,
array initialization, occurrence-index construction, queue initialization,
propagation, and the answer read. It is not a bit-Turing or Lean-VM bound.
-/
namespace LeanTrominoes.Horn.Indexed
open Worklist
variable {n : Nat}

def inputSize (input : Input n) : Nat := n+input.rules.size+premiseCount input+2

-- Dense rule enumeration, array reads, premise traversal, and constructing
-- the occurrence stream (including the temporary lists used by flatMap).
def preparationCost (input : Input n) : Nat := preparationSteps input

def totalCost (input : Input n) : Nat := preparationCost input+RAM.totalCost (edges input) (head input)

theorem linear_time (input : Input n) : totalCost input ≤ 64*inputSize input := by
  have bound := RAM.linear_bound (edges input) (head input)
  simp only [RAM.inputSize,Fintype.card_option,Fintype.card_fin,edges_length] at bound
  have preparation := preparation_bound input
  unfold totalCost preparationCost inputSize
  omega

theorem counter_bound (input : Input n) (r : RuleId input) :
    (state input).counter r ≤ premiseCount input := by
  change (solve (edges input) (head input)).counter r ≤ premiseCount input
  rw [(solve_invariant (edges input) (head input)).counters]
  exact (List.countP_le_length).trans (by rw [edges_length])

/-- The decision, agreement with the scan solver, and full RAM bound together. -/
theorem certified (input : Input n) :
    (check input=true ↔ Satisfiable input.rules.toList) ∧
    check input=Horn.check input.rules.toList ∧ totalCost input ≤ 64*inputSize input :=
  ⟨check_correct input,agrees_with_scan input,linear_time input⟩

end LeanTrominoes.Horn.Indexed
