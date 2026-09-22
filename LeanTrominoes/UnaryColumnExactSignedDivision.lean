/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnDivisionCompiler

/-! # Native signed fields for exact variable-divisor quotients -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing

theorem exact_signed_quotient (p n d : Nat) (z : Int) (positive : 0 < d)
    (exactness : (p : Int) - n = (d : Int) * z) :
    (( (p - n) / d : Nat) : Int) - ((n - p) / d : Nat) = z := by
  cases z with
  | ofNat k =>
    have h : (p : Int) - n = ((d * k : Nat) : Int) := by simpa using exactness
    have hp : p - n = d * k := by omega
    have hn : n - p = 0 := by omega
    simp [hp, hn, Nat.mul_comm d k, Nat.mul_div_left _ positive]
  | negSucc k =>
    have h : (n : Int) - p = ((d * (k + 1) : Nat) : Int) := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [Int.negSucc_eq] at exactness
      nlinarith [exactness]
    have hp : p - n = 0 := by omega
    have hn : n - p = d * (k + 1) := by omega
    simp [hp, hn, Nat.mul_comm d (k + 1), Nat.mul_div_left _ positive, Int.negSucc_eq]

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
    {rows : List Symbol → List Index} {p n : List Symbol → Index → Nat}
    {divisor : List Symbol → Nat} {value : List Symbol → Index → Int}

/-- Compile an exact signed quotient directly to the native integer encoding.
The positive and negative input columns need not be disjoint. -/
def exactSignedDivide (cp : Compiler rows p) (cn : Compiler rows n)
    (cd : ScalarCompiler divisor) (positive : ∀ s, 0 < divisor s)
    (exactness : ∀ s i, i ∈ rows s → (p s i : Int) - n s i = (divisor s : Int) * value s i) :
    Compiler rows (fun s i => Encodable.encode (value s i)) := by
  let result := signedDifference (divide (sub cp cn) cd positive) (divide (sub cn cp) cd positive)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro i hi
  exact congrArg Encodable.encode (exact_signed_quotient _ _ _ _ (positive s) (exactness s i hi))

end LeanTrominoes.UnaryColumn
end
