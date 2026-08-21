/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCounts
import Mathlib.Data.List.Enum

/-! # Stable ranks from equality rows -/

namespace LeanTrominoes
namespace StableOccurrenceRanks

variable {Value : Type*} [DecidableEq Value]

/-- Equality row of one value against the complete presentation stream. -/
def equalityRow (values : List Value) (value : Value) : List Bool :=
  values.map fun other => decide (value = other)

/-- Stable zero-based occurrence ranks, with an explicit current index. -/
def ranksAux (all : List Value) : Nat → List Value → List Nat
  | _, [] => []
  | index, value :: values =>
      (all.take index).count value :: ranksAux all (index + 1) values

/-- Each value's number of equal predecessors in presentation order. -/
def ranks (values : List Value) : List Nat :=
  ranksAux values 0 values

theorem equalityRow_prefix_trueCount
    (values : List Value) (value : Value) (index : Nat) :
    ((equalityRow values value).take index).count true =
      (values.take index).count value := by
  rw [equalityRow, ← List.map_take]
  generalize values.take index = taken
  induction taken with
  | nil => simp
  | cons head tail induction =>
      by_cases same : value = head
      · subst head
        simp [induction]
      · have headNe : head ≠ value := Ne.symm same
        simp [same, headNe, induction]

/-- Prefix-true counting over the full equality matrix computes stable
occurrence ranks. -/
theorem trueCountsAux_equalityRows
    (all remaining : List Value) (index : Nat) :
    DelimitedBinaryWordPrefixTrueCounts.countsAux index
        (remaining.map (equalityRow all)) =
      ranksAux all index remaining := by
  induction remaining generalizing index with
  | nil => rfl
  | cons value remaining induction =>
      simp only [List.map_cons,
        DelimitedBinaryWordPrefixTrueCounts.countsAux_cons,
        DelimitedBinaryWordPrefixTrueCounts.count, ranksAux]
      rw [equalityRow_prefix_trueCount, induction]

/-- The public row-prefix operation computes stable occurrence ranks. -/
theorem trueCounts_equalityRows (values : List Value) :
    DelimitedBinaryWordPrefixTrueCounts.counts
        ⟨values.map (equalityRow values)⟩ =
      ranks values := by
  exact trueCountsAux_equalityRows values values 0

/-- Equivalent indexed presentation of the stable-rank list. -/
theorem ranksAux_eq_map_zipIdx
    (all remaining : List Value) (index : Nat) :
    ranksAux all index remaining =
      (remaining.zipIdx index).map fun tagged =>
        (all.take tagged.2).count tagged.1 := by
  induction remaining generalizing index with
  | nil => rfl
  | cons value remaining induction =>
      simp only [ranksAux, List.zipIdx_cons, List.map_cons]
      rw [induction]

theorem ranks_eq_map_zipIdx (values : List Value) :
    ranks values =
      values.zipIdx.map fun tagged =>
        (values.take tagged.2).count tagged.1 := by
  exact ranksAux_eq_map_zipIdx values values 0

end StableOccurrenceRanks
end LeanTrominoes
