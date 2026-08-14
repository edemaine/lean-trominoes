/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SelectedPrefixMarkerTime

/-!
# Finite intervals of prefix-marked selected items

The prefix marker already exposes the suffix after a fixed selected prefix.
Complement it with selectors for the first fixed prefix and for a fixed
half-open interval of selected-occurrence indices, together with their exact
selected counts.
-/

namespace LeanTrominoes

namespace SelectedPrefixMarkerMachine

/-- The marker's final control count is the initial count plus all selected
items, capped at the fixed cutoff. -/
theorem countAfter_val {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (count : Count cutoff) (data : List Data) :
    (countAfter selected count data).val =
      min cutoff
        (count.val + UnaryPolynomialPaddingMachine.selectedCount selected data) := by
  induction data generalizing count with
  | nil =>
      simp [countAfter, UnaryPolynomialPaddingMachine.selectedCount,
        Nat.min_eq_right (Nat.le_of_lt_succ count.isLt)]
  | cons item data induction =>
      cases selectedEq : selected item with
      | false =>
          simp [countAfter, nextCount, selectedEq,
            UnaryPolynomialPaddingMachine.selectedCount, induction]
      | true =>
          by_cases below : count.val < cutoff
          · rw [countAfter,
              UnaryPolynomialPaddingMachine.selectedCount_cons,
              induction]
            rw [nextCount_val_of_selected_lt selected item count
              selectedEq below]
            simp [selectedEq]
            congr 1
            omega
          · have countEq : count.val = cutoff := by
              have countLe : count.val ≤ cutoff :=
                Nat.le_of_lt_succ count.isLt
              omega
            rw [countAfter,
              UnaryPolynomialPaddingMachine.selectedCount_cons,
              induction]
            simp [nextCount, selectedEq, capSucc, countEq]

@[simp]
theorem countAfter_zeroCount_val {Data : Type} (selected : Data → Bool)
    (cutoff : Nat) (data : List Data) :
    (countAfter selected (zeroCount cutoff) data).val =
      min cutoff (UnaryPolynomialPaddingMachine.selectedCount selected data) := by
  simpa [zeroCount] using
    countAfter_val selected (zeroCount cutoff) data

/-- Select original items among the first `stop` selected occurrences. -/
def beforePrefix {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (stop : Nat) : Tagged cutoff Data → Bool
  | (data, count) => selected data && decide (count.val < stop)

/-- Select original items whose zero-based selected-occurrence index lies in
the half-open interval `[start, stop)`. -/
def betweenPrefixes {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (start stop : Nat) : Tagged cutoff Data → Bool
  | (data, count) =>
      selected data && decide (start ≤ count.val ∧ count.val < stop)

/-- Select the single selected occurrence at zero-based index `position`, if
that occurrence exists. -/
def atPrefix {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (position : Nat) : Tagged cutoff Data → Bool :=
  betweenPrefixes selected position (position + 1)

theorem selectedCount_fst_markAux {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (count : Count cutoff) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount
        (fun tagged : Tagged cutoff Data => selected tagged.1)
        (markAux selected count data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  induction data generalizing count with
  | nil => rfl
  | cons item data induction =>
      simp [markAux, UnaryPolynomialPaddingMachine.selectedCount, induction]

@[simp]
theorem selectedCount_fst_mark {Data : Type} (selected : Data → Bool)
    (cutoff : Nat) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount
        (fun tagged : Tagged cutoff Data => selected tagged.1)
        (mark selected cutoff data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  exact selectedCount_fst_markAux selected (zeroCount cutoff) data

theorem selectedCount_before_add_after {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (stop : Nat)
    (data : List (Tagged cutoff Data)) :
    UnaryPolynomialPaddingMachine.selectedCount
          (beforePrefix selected stop) data +
        UnaryPolynomialPaddingMachine.selectedCount
          (afterPrefix selected stop) data =
      UnaryPolynomialPaddingMachine.selectedCount
        (fun tagged : Tagged cutoff Data => selected tagged.1) data := by
  induction data with
  | nil => rfl
  | cons tagged data induction =>
      rcases tagged with ⟨item, count⟩
      cases selectedEq : selected item with
      | false =>
          simpa [UnaryPolynomialPaddingMachine.selectedCount,
            beforePrefix, afterPrefix, selectedEq] using induction
      | true =>
          by_cases below : count.val < stop
          · simp [UnaryPolynomialPaddingMachine.selectedCount,
              beforePrefix, afterPrefix, selectedEq, below,
              Nat.not_le.mpr below]
            omega
          · have reached : stop ≤ count.val := Nat.le_of_not_gt below
            simp [UnaryPolynomialPaddingMachine.selectedCount,
              beforePrefix, afterPrefix, selectedEq, below, reached]
            omega

/-- Exactly the first `min total stop` selected occurrences are before the
fixed prefix boundary. -/
theorem selectedCount_beforePrefix_mark {Data : Type}
    (selected : Data → Bool) {cutoff stop : Nat}
    (stopLe : stop ≤ cutoff) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount
        (beforePrefix selected stop) (mark selected cutoff data) =
      min (UnaryPolynomialPaddingMachine.selectedCount selected data) stop := by
  have partition := selectedCount_before_add_after selected stop
    (mark selected cutoff data)
  rw [selectedCount_fst_mark,
    selectedCount_afterPrefix_mark selected stopLe] at partition
  rw [Nat.min_def]
  split <;> omega

theorem selectedCount_between_add_after {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) {start stop : Nat} (startLe : start ≤ stop)
    (data : List (Tagged cutoff Data)) :
    UnaryPolynomialPaddingMachine.selectedCount
          (betweenPrefixes selected start stop) data +
        UnaryPolynomialPaddingMachine.selectedCount
          (afterPrefix selected stop) data =
      UnaryPolynomialPaddingMachine.selectedCount
        (afterPrefix selected start) data := by
  induction data with
  | nil => rfl
  | cons tagged data induction =>
      rcases tagged with ⟨item, count⟩
      cases selectedEq : selected item with
      | false =>
          simpa [UnaryPolynomialPaddingMachine.selectedCount,
            betweenPrefixes, afterPrefix, selectedEq] using induction
      | true =>
          by_cases reachedStart : start ≤ count.val
          · by_cases belowStop : count.val < stop
            · simp [UnaryPolynomialPaddingMachine.selectedCount,
                betweenPrefixes, afterPrefix, selectedEq, reachedStart,
                belowStop, Nat.not_le.mpr belowStop]
              omega
            · have reachedStop : stop ≤ count.val :=
                Nat.le_of_not_gt belowStop
              simp [UnaryPolynomialPaddingMachine.selectedCount,
                betweenPrefixes, afterPrefix, selectedEq, reachedStart,
                belowStop, reachedStop]
              omega
          · have belowStart : count.val < start := Nat.lt_of_not_ge reachedStart
            have belowStop : count.val < stop := belowStart.trans_le startLe
            simp [UnaryPolynomialPaddingMachine.selectedCount,
              betweenPrefixes, afterPrefix, selectedEq, reachedStart,
              Nat.not_le.mpr belowStop, induction]

/-- The marked half-open interval has the corresponding difference of
truncated suffix counts. -/
theorem selectedCount_betweenPrefixes_mark {Data : Type}
    (selected : Data → Bool) {cutoff start stop : Nat}
    (startLe : start ≤ stop) (stopLe : stop ≤ cutoff) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount
        (betweenPrefixes selected start stop) (mark selected cutoff data) =
      (UnaryPolynomialPaddingMachine.selectedCount selected data - start) -
        (UnaryPolynomialPaddingMachine.selectedCount selected data - stop) := by
  have partition := selectedCount_between_add_after selected startLe
    (mark selected cutoff data)
  have startCutoff : start ≤ cutoff := startLe.trans stopLe
  rw [selectedCount_afterPrefix_mark selected stopLe,
    selectedCount_afterPrefix_mark selected startCutoff] at partition
  omega

/-- A fixed marked occurrence contributes one selected item exactly when its
index is below the original selected count. -/
theorem selectedCount_atPrefix_mark {Data : Type}
    (selected : Data → Bool) {cutoff position : Nat}
    (positionLe : position + 1 ≤ cutoff) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount
        (atPrefix selected position) (mark selected cutoff data) =
      if position < UnaryPolynomialPaddingMachine.selectedCount selected data
      then 1 else 0 := by
  unfold atPrefix
  rw [selectedCount_betweenPrefixes_mark selected (Nat.le_succ position)
    positionLe]
  split <;> omega

end SelectedPrefixMarkerMachine
end LeanTrominoes
