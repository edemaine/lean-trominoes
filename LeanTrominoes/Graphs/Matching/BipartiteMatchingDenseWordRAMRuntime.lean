/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMProgram

/-! # A uniform polynomial bound including preparation and halt -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM

theorem runtime_quartic (input : Input) (cost : Nat)
    (budget : cost≤(120*(input.1+1)^2*(input.2.2.length+1)+5)*input.1+5) :
    4*(2*input.1+input.2.1+2*(input.1*input.1))+58+cost+1≤1000*(size input+1)^4 := by
  let x := size input+1
  have positive : 1≤x := by dsimp [x,size]; omega
  have nBound : input.1≤x := by dsimp [x,size]; omega
  have mBound : input.2.1≤x := by dsimp [x,size]; omega
  have npBound : input.1+1≤x := by dsimp [x,size]; omega
  have epBound : input.2.2.length+1≤x := by dsimp [x,size]; omega
  have square : input.1^2≤x^2 := Nat.pow_le_pow_left nBound 2
  have xSquare : x≤x^2 := by nlinarith
  have squarePositive : 1≤x^2 := by nlinarith
  have product : (input.1+1)^2*(input.2.2.length+1)*input.1≤x^4 := by
    have bound := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left npBound 2) epBound) nBound
    convert bound using 1; ring
  have small : 13*input.1+4*input.2.1+8*(input.1*input.1)+64≤100*x^2 := by nlinarith
  have total : 4*(2*input.1+input.2.1+2*(input.1*input.1))+58+cost+1≤120*x^4+100*x^2 := by nlinarith
  have second : x^2≤x^4 := by
    have bound := Nat.mul_le_mul_left (x^2) squarePositive
    convert bound using 1 <;> ring
  exact total.trans (by dsimp [x] at *; omega)

/-- A weaker bound retained for callers using the original certificate. -/
theorem runtime_polynomial (input : Input) (cost : Nat)
    (budget : cost≤(120*(input.1+1)^2*(input.2.2.length+1)+5)*input.1+5) :
    4*(2*input.1+input.2.1+2*(input.1*input.1))+58+cost+1≤1000*(size input+1)^5 := by
  have grow : (size input+1)^4≤(size input+1)^5 := by
    have bound := Nat.mul_le_mul_left ((size input+1)^4) (show 1≤size input+1 by omega)
    simpa only [Nat.mul_one,pow_succ] using bound
  exact (runtime_quartic input cost budget).trans (Nat.mul_le_mul_left 1000 grow)

end LeanTrominoes.BipartiteMatching.DenseWordRAM
