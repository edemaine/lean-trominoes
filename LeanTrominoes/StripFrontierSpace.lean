/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StripFrontier
import LeanTrominoes.FiniteStateReachability

/-!
# Sparse strip-frontier state bounds

The five-column frontier representation stores one of nine assignment values
at each distinct motif cell and column, plus a horizontal phase.  This file
computes its exact cardinality and bounds the logarithmic Savitch recursion
depth linearly in the motif size and the binary length of the period.
-/

open LeanTrominoes

namespace LeanTrominoes.PeriodicStrip.WindowState

def equivData (periodicStrip : PeriodicStrip) :
    WindowState periodicStrip ≃
      Fin periodicStrip.period ×
        (WindowColumn → periodicStrip.MotifCell → Option SquareSymmetry) where
  toFun state := (state.phase, state.assignment)
  invFun data := ⟨data.1, data.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem windowState_card (periodicStrip : PeriodicStrip) :
    Fintype.card (WindowState periodicStrip) =
      periodicStrip.period *
        9 ^ (5 * periodicStrip.motif.toFinset.card) := by
  rw [Fintype.card_congr (equivData periodicStrip)]
  have symmetryCard : Fintype.card SquareSymmetry = 8 := by
    native_decide
  have motifCard :
      Fintype.card periodicStrip.MotifCell =
        periodicStrip.motif.toFinset.card :=
    Fintype.card_coe _
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_option]
  rw [symmetryCard, motifCard]
  simp [pow_mul, Nat.mul_comm]

theorem windowState_card_le_pow (periodicStrip : PeriodicStrip) :
    Fintype.card (WindowState periodicStrip) ≤
      2 ^ (Nat.clog 2 periodicStrip.period +
        20 * periodicStrip.motif.toFinset.card) := by
  rw [windowState_card]
  calc
    periodicStrip.period *
          9 ^ (5 * periodicStrip.motif.toFinset.card) ≤
        2 ^ Nat.clog 2 periodicStrip.period *
          (2 ^ 4) ^ (5 * periodicStrip.motif.toFinset.card) :=
      Nat.mul_le_mul
        (Nat.le_pow_clog Nat.one_lt_two periodicStrip.period)
        (Nat.pow_le_pow_left (by omega) _)
    _ = 2 ^ (Nat.clog 2 periodicStrip.period +
        20 * periodicStrip.motif.toFinset.card) := by
      rw [← pow_mul, ← pow_add]
      congr 2
      omega

theorem savitchDepth_windowState_le (periodicStrip : PeriodicStrip) :
    FiniteState.savitchDepth (WindowState periodicStrip) ≤
      Nat.clog 2 periodicStrip.period +
        20 * periodicStrip.motif.toFinset.card + 1 := by
  unfold FiniteState.savitchDepth
  apply Nat.succ_le_succ
  calc
    Nat.log 2 (Fintype.card (WindowState periodicStrip)) ≤
        Nat.log 2
          (2 ^ (Nat.clog 2 periodicStrip.period +
            20 * periodicStrip.motif.toFinset.card)) :=
      Nat.log_mono_right (windowState_card_le_pow periodicStrip)
    _ = Nat.clog 2 periodicStrip.period +
        20 * periodicStrip.motif.toFinset.card :=
      Nat.log_pow Nat.one_lt_two _

end LeanTrominoes.PeriodicStrip.WindowState
