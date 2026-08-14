/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SelectedPrefixMarkerMachine
import LeanTrominoes.UnaryPolynomialPaddingMachine

/-!
# Semantics and runtime of selected-prefix marking

The capped tag is sufficient to skip any fixed selected prefix no longer than
the cutoff.  The corresponding selector has count exactly `count - skip`, and
the verified marker runs in linear time.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace SelectedPrefixMarkerMachine

/-- Select original items whose zero-based selected-occurrence index is at
least `skip`. -/
def afterPrefix {Data : Type} (selected : Data → Bool) (skip : Nat) :
    Tagged cutoff Data → Bool
  | (data, count) => selected data && decide (skip ≤ count.val)

theorem count_val_le_capSucc {cutoff : Nat} (count : Count cutoff) :
    count.val ≤ (capSucc count).val := by
  unfold capSucc
  split
  · simp
  · rfl

theorem count_val_le_nextCount {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (data : Data) (count : Count cutoff) :
    count.val ≤ (nextCount selected data count).val := by
  unfold nextCount
  split
  · exact count_val_le_capSucc count
  · rfl

theorem nextCount_val_of_selected_lt {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (data : Data) (count : Count cutoff)
    (selectedData : selected data = true) (below : count.val < cutoff) :
    (nextCount selected data count).val = count.val + 1 := by
  simp [nextCount, selectedData, capSucc, below]

theorem selectedCount_markAux {Data : Type} {cutoff skip : Nat}
    (selected : Data → Bool) (skipLe : skip ≤ cutoff)
    (count : Count cutoff) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount
        (afterPrefix selected skip) (markAux selected count data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data -
        (skip - count.val) := by
  induction data generalizing count with
  | nil => simp [markAux, UnaryPolynomialPaddingMachine.selectedCount]
  | cons item data induction =>
      cases selectedEq : selected item with
      | false =>
          simpa [markAux, UnaryPolynomialPaddingMachine.selectedCount,
            afterPrefix, nextCount, selectedEq] using induction count
      | true =>
          by_cases reached : skip ≤ count.val
          · have reachedNext :
                skip ≤ (nextCount selected item count).val :=
              reached.trans (count_val_le_nextCount selected item count)
            rw [markAux,
              UnaryPolynomialPaddingMachine.selectedCount_cons,
              UnaryPolynomialPaddingMachine.selectedCount_cons,
              induction (nextCount selected item count)]
            simp [afterPrefix, selectedEq, reached, reachedNext]
          · have countLtSkip : count.val < skip := Nat.lt_of_not_ge reached
            have countLtCutoff : count.val < cutoff :=
              countLtSkip.trans_le skipLe
            have nextValue : (nextCount selected item count).val =
                count.val + 1 :=
              nextCount_val_of_selected_lt selected item count selectedEq
                countLtCutoff
            rw [markAux,
              UnaryPolynomialPaddingMachine.selectedCount_cons,
              UnaryPolynomialPaddingMachine.selectedCount_cons,
              induction (nextCount selected item count)]
            simp [afterPrefix, selectedEq, reached, nextValue]
            omega

/-- After marking with cutoff `cutoff`, the selector that skips `skip`
selected items has exactly the truncated-subtraction count. -/
theorem selectedCount_afterPrefix_mark {Data : Type}
    (selected : Data → Bool) {cutoff skip : Nat}
    (skipLe : skip ≤ cutoff) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount
        (afterPrefix selected skip) (mark selected cutoff data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data - skip := by
  simpa [mark, zeroCount] using
    selectedCount_markAux selected skipLe (zeroCount cutoff) data

@[simp]
theorem map_fst_markAux {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (count : Count cutoff) (data : List Data) :
    (markAux selected count data).map Prod.fst = data := by
  induction data generalizing count with
  | nil => rfl
  | cons item data induction => simp [markAux, induction]

@[simp]
theorem map_fst_mark {Data : Type} (selected : Data → Bool)
    (cutoff : Nat) (data : List Data) :
    (mark selected cutoff data).map Prod.fst = data := by
  simp [mark]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 2

@[simp]
theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 2 * length + 2 := by
  simp [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul]

/-- Selected-prefix marking is polynomial-time (indeed linear-time) for every
fixed finite cutoff. -/
noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (cutoff : Nat) :
    @TM2ComputableInPolyTime
      (List Data) (List (Tagged cutoff Data)) Data (Tagged cutoff Data)
      id id (mark selected cutoff) where
  tm := machine cutoff Data selected
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial
  outputsFun data := by
    have run := machine_outputsInTime (cutoff := cutoff) selected data
    have run' : TM2OutputsInTime (machine cutoff Data selected)
        (List.map (Equiv.refl Data).invFun (id data))
        (some (List.map (Equiv.refl (Tagged cutoff Data)).invFun
          (id (mark selected cutoff data))))
        (2 * data.length + 2) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    rw [timePolynomial_eval]
    exact run'

end SelectedPrefixMarkerMachine
end LeanTrominoes
