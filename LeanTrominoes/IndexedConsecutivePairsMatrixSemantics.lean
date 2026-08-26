/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsSemantics
import LeanTrominoes.ListZipIdxFilterAt

/-! # Row-major successor matrices enumerate adjacent pairs -/

namespace LeanTrominoes.IndexedConsecutivePairs

private theorem filterMap_if_some_eq_filter_map
    {Value Output : Type*} (values : List Value)
    (selected : Value → Bool) (output : Value → Output) :
    values.filterMap (fun value =>
        if selected value then some (output value) else none) =
      (values.filter selected).map output := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      cases active : selected value <;> simp [active, induction]

private theorem filterMap_zipIdx_eq_add_index
    {Value Output : Type*} (values : List Value)
    (start offset : Nat) (selected : Value → Bool)
    (output : Value → Output) :
    (values.zipIdx start).filterMap (fun tagged =>
        if decide (start + offset = tagged.2) && selected tagged.1 then
          some (output tagged.1)
        else none) =
      match values[offset]? with
      | some value => if selected value then [output value] else []
      | none => [] := by
  rw [filterMap_if_some_eq_filter_map]
  rw [show (values.zipIdx start).filter (fun tagged =>
        decide (start + offset = tagged.2) && selected tagged.1) =
      ((values.zipIdx start).filter fun tagged =>
        decide (start + offset = tagged.2)).filter fun tagged =>
          selected tagged.1 by
    rw [List.filter_filter]
    apply List.filter_congr
    intro tagged _taggedMember
    simp only [Bool.and_comm]]
  rw [List.filter_zipIdx_eq_add_index]
  cases lookup : values[offset]? with
  | none => rfl
  | some value =>
      cases active : selected value <;> simp [active]

private theorem start_le_snd_of_mem_zipIdx
    {Value : Type*} (values : List Value) (start : Nat)
    (tagged : Value × Nat) (member : tagged ∈ values.zipIdx start) :
    start ≤ tagged.2 := by
  induction values generalizing start with
  | nil => simp at member
  | cons value values induction =>
      simp only [List.zipIdx_cons, List.mem_cons] at member
      rcases member with equal | member
      · subst tagged
        exact Nat.le_refl start
      · exact Nat.le_trans (by omega)
          (induction (start + 1) member)

/-- Scanning the square indexed product in row-major order and retaining only
index-successor entries gives exactly the usual adjacent-pair scan, with any
additional pointwise selection preserved. -/
theorem zipIdx_successorMatrix_filterMap
    {Value Output : Type*} (values : List Value)
    (selected : Value → Value → Bool)
    (output : Value → Value → Output) :
    values.zipIdx.flatMap (fun first =>
        values.zipIdx.filterMap fun second =>
          if decide (second.2 = first.2 + 1) &&
              selected first.1 second.1 then
            some (output first.1 second.1)
          else none) =
      (pairs values).filterMap fun pair =>
        if selected pair.1 pair.2 then
          some (output pair.1 pair.2)
        else none := by
  rw [pairs_eq_consecutivePairs]
  suffices statement : ∀ start,
      (values.zipIdx start).flatMap (fun first =>
          (values.zipIdx start).filterMap fun second =>
            if decide (second.2 = first.2 + 1) &&
                selected first.1 second.1 then
              some (output first.1 second.1)
            else none) =
        (PeriodicOrthocrossing.consecutivePairs values).filterMap fun pair =>
          if selected pair.1 pair.2 then
            some (output pair.1 pair.2)
          else none by
    exact statement 0
  intro start
  induction values generalizing start with
  | nil => rfl
  | cons first rest induction =>
      cases rest with
      | nil =>
          simp [PeriodicOrthocrossing.consecutivePairs]
      | cons second rest =>
          rw [List.zipIdx_cons, List.flatMap_cons]
          have firstRow := filterMap_zipIdx_eq_add_index
            (first :: second :: rest) start 1
            (selected first) (output first)
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Nat.add_comm start 1] at firstRow
          rw [show ((first, start) :: (second :: rest).zipIdx (start + 1)).filterMap
                (fun tagged =>
                  if decide (tagged.2 = start + 1) &&
                      selected first tagged.1 then
                    some (output first tagged.1)
                  else none) =
              (if selected first second then
                [output first second]
              else []) by
            simpa only [List.zipIdx_cons, Nat.add_comm, eq_comm] using firstRow]
          have tailRows :
              ((second :: rest).zipIdx (start + 1)).flatMap (fun row =>
                  ((first, start) ::
                      (second :: rest).zipIdx (start + 1)).filterMap
                    fun column =>
                      if decide (column.2 = row.2 + 1) &&
                          selected row.1 column.1 then
                        some (output row.1 column.1)
                      else none) =
                ((second :: rest).zipIdx (start + 1)).flatMap (fun row =>
                  ((second :: rest).zipIdx (start + 1)).filterMap
                    fun column =>
                      if decide (column.2 = row.2 + 1) &&
                          selected row.1 column.1 then
                        some (output row.1 column.1)
                      else none) := by
            apply List.flatMap_congr
            intro row rowMember
            have rowLower := start_le_snd_of_mem_zipIdx
              (second :: rest) (start + 1) row rowMember
            simp only [List.filterMap_cons]
            rw [show decide (start = row.2 + 1) = false by
              simp [show start ≠ row.2 + 1 by omega]]
            rfl
          rw [tailRows, induction (start + 1)]
          cases active : selected first second <;>
            simp [PeriodicOrthocrossing.consecutivePairs, active]

end LeanTrominoes.IndexedConsecutivePairs
