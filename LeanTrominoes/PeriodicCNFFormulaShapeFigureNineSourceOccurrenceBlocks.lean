/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrences

/-! # Concatenating coherent Figure 9 occurrence blocks -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering

/-- Parent profiles in traversal order; variable markers consume no parent
or tail-table row. -/
def sourceOccurrenceProfiles : List Token → List DirectedClauseProfile
  | [] => []
  | .variable :: source => sourceOccurrenceProfiles source
  | .clause profile :: source => profile :: sourceOccurrenceProfiles source

@[simp] theorem sourceOccurrenceProfiles_map_clauses {α : Type*}
    (values : List α) (profile : α → DirectedClauseProfile) :
    sourceOccurrenceProfiles (values.map (fun value => Token.clause (profile value))) = values.map profile := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.map_cons, sourceOccurrenceProfiles, ih]

/-- Concatenating descriptor blocks preserves every occurrence record, with
both clause counters and the consumed tail rows advanced by the first block. -/
theorem sourceOccurrencesFrom_append
    (parent start : Nat) (first second : List Token)
    (tails : List (List (List AxisDirection))) :
    sourceOccurrencesFrom parent start (first ++ second) tails =
      sourceOccurrencesFrom parent start first tails ++
      sourceOccurrencesFrom (parent + (sourceOccurrenceProfiles first).length)
        (start + ((sourceOccurrenceProfiles first).map generatedClauseCount).sum)
        second (tails.drop (sourceOccurrenceProfiles first).length) := by
  induction first generalizing parent start tails with
  | nil => simp [sourceOccurrencesFrom, sourceOccurrenceProfiles]
  | cons token first ih =>
      cases token with
      | «variable» =>
          simpa only [List.cons_append, sourceOccurrencesFrom, sourceOccurrenceProfiles] using
            ih parent start tails
      | clause profile =>
          simp only [List.cons_append, sourceOccurrencesFrom, sourceOccurrenceProfiles,
            List.length_cons, List.map_cons, List.sum_cons, ih, List.append_assoc]
          simp only [Nat.add_assoc, Nat.add_comm, List.drop_tail]

private theorem sourceOccurrencesFrom_variables
    (parent start count : Nat) (tails : List (List (List AxisDirection))) :
    sourceOccurrencesFrom parent start (List.replicate count Token.variable) tails = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ, sourceOccurrencesFrom] using ih

/-- Trailing variable markers neither create records nor alter the records
of any preceding copied or cycle clause. -/
theorem sourceOccurrencesFrom_append_variables
    (parent start : Nat) (source : List Token) (count : Nat)
    (tails : List (List (List AxisDirection))) :
    sourceOccurrencesFrom parent start (source ++ List.replicate count Token.variable) tails =
      sourceOccurrencesFrom parent start source tails := by
  rw [sourceOccurrencesFrom_append, sourceOccurrencesFrom_variables, List.append_nil]

theorem sourceOccurrences_append_variables
    (source : List Token) (count : Nat) (tails : List (List (List AxisDirection))) :
    sourceOccurrences (source ++ List.replicate count Token.variable) tails =
      sourceOccurrences source tails :=
  sourceOccurrencesFrom_append_variables 0 0 source count tails

/-- Every genuine record's parent lies within its own descriptor block's
parent interval, independently of generated-clause and tail-table sizes. -/
theorem sourceOccurrencesFrom_parent_lt
    (parent start : Nat) (source : List Token) (tails : List (List (List AxisDirection)))
    (occurrence : SourceOccurrence)
    (member : occurrence ∈ sourceOccurrencesFrom parent start source tails) :
    occurrence.parentClauseIndex < parent + (sourceOccurrenceProfiles source).length := by
  induction source generalizing parent start tails with
  | nil => simp only [sourceOccurrencesFrom, List.not_mem_nil] at member
  | cons token source ih =>
      cases token with
      | «variable» => exact ih parent start tails member
      | clause profile =>
          rw [sourceOccurrencesFrom, List.mem_append] at member
          rcases member with member | member
          · obtain ⟨header, _headerMember, rfl⟩ := List.mem_map.mp member
            simp only [sourceOccurrenceProfiles, List.length_cons]
            omega
          · have bound := ih (parent + 1) (start + generatedClauseCount profile) tails.tail member
            simpa only [sourceOccurrenceProfiles, List.length_cons,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using bound

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
