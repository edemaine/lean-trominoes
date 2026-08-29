/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Defs

/-! # Flattening optional list-valued matrix blocks -/

namespace List

private theorem optionalBlocks_project_flatten
    {Value Element Output : Type*}
    (values : List Value)
    (predicate : Value → Bool)
    (block : Value → List Element)
    (project : List Element → List Output)
    (projectNil : project [] = []) :
    ((values.map fun value =>
        if predicate value then block value else []).map project).flatten =
      ((values.filterMap fun value =>
        if predicate value then some (block value) else none).map
          project).flatten := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      cases active : predicate value with
      | false =>
          simp only [List.map_cons, List.filterMap_cons, active,
            Bool.false_eq_true, ↓reduceIte, List.flatten_cons]
          rw [projectNil, List.nil_append, induction]
      | true =>
          simp only [List.map_cons, List.filterMap_cons, active,
            ↓reduceIte, List.flatten_cons]
          rw [induction]

/-- Mapping a projection that sends the empty block to the empty list, then
flattening, erases inactive matrix cells just as `filterMap` does. -/
theorem matrixOptionalBlocks_project_flatten
    {Row Column Element Output : Type*}
    (rows : List Row) (columns : List Column)
    (predicate : Row → Column → Bool)
    (block : Row → Column → List Element)
    (project : List Element → List Output)
    (projectNil : project [] = []) :
    (((rows.flatMap fun first =>
        columns.map fun second =>
          if predicate first second then block first second else []).map
            project).flatten) =
      (((rows.flatMap fun first =>
        columns.filterMap fun second =>
          if predicate first second then some (block first second)
          else none).map project).flatten) := by
  induction rows with
  | nil => rfl
  | cons row rows induction =>
      simp only [List.flatMap_cons, List.map_append, List.flatten_append]
      rw [optionalBlocks_project_flatten columns (predicate row)
        (block row) project projectNil, induction]

end List
