/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.ProdSigma

/-! # Filtering Cartesian products of optional list entries -/

namespace List

universe uα uβ uγ uδ

variable {α : Type uα} {β : Type uβ}
variable {γ : Type uγ} {δ : Type uδ}

/-- Keep a pair of optional values exactly when both exist and satisfy a
Boolean predicate. -/
def optionalFilteredPair
    (predicate : α × β → Bool)
    (first : Option α) (second : Option β) : Option (α × β) :=
  match first, second with
  | some firstValue, some secondValue =>
      if predicate (firstValue, secondValue) then
        some (firstValue, secondValue)
      else
        none
  | _, _ => none

/-- Optional filtering of one fixed first value commutes with filtering the
second list before forming the product row. -/
theorem optionalFilteredRow
    (predicate : α × β → Bool) (first : α)
    (seconds : List γ) (secondValue : γ → Option β) :
    seconds.filterMap (fun second =>
        optionalFilteredPair predicate (some first)
          (secondValue second)) =
      ((seconds.filterMap secondValue).map fun second =>
        (first, second)).filter predicate := by
  induction seconds with
  | nil => rfl
  | cons second seconds induction =>
      cases lookup : secondValue second with
      | none =>
          have headEq :
              optionalFilteredPair predicate (some first)
                (secondValue second) = none := by
            simp [optionalFilteredPair, lookup]
          rw [List.filterMap_cons, headEq,
            List.filterMap_cons, lookup]
          simpa using induction
      | some value =>
          cases accepted : predicate (first, value) with
          | false =>
              have headEq :
                  optionalFilteredPair predicate (some first)
                    (secondValue second) = none := by
                simp [optionalFilteredPair, lookup, accepted]
              rw [List.filterMap_cons, headEq,
                List.filterMap_cons, lookup]
              simp only [List.map_cons, List.filter_cons, accepted,
                Bool.false_eq_true, if_false]
              exact induction
          | true =>
              have headEq :
                  optionalFilteredPair predicate (some first)
                    (secondValue second) = some (first, value) := by
                simp [optionalFilteredPair, lookup, accepted]
              rw [List.filterMap_cons, headEq,
                List.filterMap_cons, lookup]
              simp only [List.map_cons, List.filter_cons, accepted,
                if_true, List.cons.injEq, true_and]
              exact induction

/-- Filtering optional values after forming a Cartesian product is exactly
the filtered product of the independently compacted input lists. -/
theorem optionalFilteredProduct
    (predicate : α × β → Bool)
    (firsts : List γ) (seconds : List δ)
    (firstValue : γ → Option α)
    (secondValue : δ → Option β) :
    (firsts ×ˢ seconds).filterMap (fun pair =>
        optionalFilteredPair predicate
          (firstValue pair.1) (secondValue pair.2)) =
      ((firsts.filterMap firstValue) ×ˢ
        (seconds.filterMap secondValue)).filter predicate := by
  induction firsts with
  | nil => rfl
  | cons first firsts induction =>
      cases lookup : firstValue first with
      | none =>
          have rowEq :
              (seconds.map fun second => (first, second)).filterMap
                  (fun pair => optionalFilteredPair predicate
                    (firstValue pair.1) (secondValue pair.2)) = [] := by
            rw [List.filterMap_map, List.filterMap_eq_nil_iff]
            intro second _
            simp [optionalFilteredPair, lookup]
          rw [List.product_cons, List.filterMap_append, rowEq,
            List.nil_append, List.filterMap_cons, lookup]
          simpa using induction
      | some value =>
          have rowEq :
              (seconds.map fun second => (first, second)).filterMap
                  (fun pair => optionalFilteredPair predicate
                    (firstValue pair.1) (secondValue pair.2)) =
                ((seconds.filterMap secondValue).map fun second =>
                  (value, second)).filter predicate := by
            rw [List.filterMap_map]
            change seconds.filterMap (fun second =>
                optionalFilteredPair predicate (firstValue first)
                  (secondValue second)) = _
            rw [lookup]
            exact optionalFilteredRow predicate value seconds secondValue
          rw [List.product_cons, List.filterMap_append, rowEq,
            List.filterMap_cons, lookup, List.product_cons,
            List.filter_append, induction]

end List
