/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Periodic
import Mathlib.Computability.Primrec.List

/-!
# Computability support

Primitive-recursive signed arithmetic for Mathlib's canonical encoding of
integers. Nonnegative `n` has code `2*n`; negative `-(n+1)` has code `2*n+1`.
These lemmas support certified finite search over periodic regions.
-/

namespace LeanTrominoes.Computability

open Encodable

noncomputable instance : Primcodable SquareSymmetry :=
  Primcodable.ofEquiv (Fin (Fintype.card SquareSymmetry))
    (Fintype.equivFin SquareSymmetry)

@[simp]
theorem encode_int_ofNat (n : Nat) : encode (Int.ofNat n) = 2 * n := by
  rfl

@[simp]
theorem encode_int_negSucc (n : Nat) : encode (Int.negSucc n) = 2 * n + 1 := by
  rfl

/-- Sign bit of an encoded integer. -/
def intCodeNegative (code : Nat) : Bool :=
  code.bodd

/-- Absolute value of an encoded integer. -/
def intCodeMagnitude (code : Nat) : Nat :=
  bif code.bodd then code.div2 + 1 else code.div2

/-- Encode a sign and magnitude, normalizing both signed zeroes to zero. -/
def intCodeOfSignMagnitude (negative : Bool) (magnitude : Nat) : Nat :=
  if magnitude = 0 then
    0
  else bif negative then
    2 * (magnitude - 1) + 1
  else
    2 * magnitude

theorem intCodeNegative_primrec : Primrec intCodeNegative :=
  Primrec.nat_bodd

theorem intCodeMagnitude_primrec : Primrec intCodeMagnitude := by
  unfold intCodeMagnitude
  exact Primrec.cond Primrec.nat_bodd
    (Primrec.nat_add.comp Primrec.nat_div2 (Primrec.const 1))
    Primrec.nat_div2

theorem intCodeOfSignMagnitude_primrec : Primrec₂ intCodeOfSignMagnitude := by
  change Primrec fun input : Bool × Nat => intCodeOfSignMagnitude input.1 input.2
  unfold intCodeOfSignMagnitude
  apply Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
  · exact Primrec.const 0
  · exact Primrec.cond Primrec.fst
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
        (Primrec.const 1))
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)

theorem intCode_roundtrip (integer : Int) :
    intCodeOfSignMagnitude
      (intCodeNegative (encode integer))
      (intCodeMagnitude (encode integer)) = encode integer := by
  cases integer with
  | ofNat n =>
      rw [encode_int_ofNat]
      simp [intCodeOfSignMagnitude, intCodeNegative, intCodeMagnitude,
        Nat.bodd, Nat.div2]
  | negSucc n =>
      rw [encode_int_negSucc]
      simp [intCodeOfSignMagnitude, intCodeNegative, intCodeMagnitude,
        Nat.bodd, Nat.div2]
      simpa [Nat.bit_val] using Nat.bit_div_two true n

@[simp]
theorem intCodeNegative_encode_ofNat (n : Nat) :
    intCodeNegative (encode (Int.ofNat n)) = false := by
  rw [encode_int_ofNat]
  simp [intCodeNegative, Nat.bodd]

@[simp]
theorem intCodeNegative_encode_negSucc (n : Nat) :
    intCodeNegative (encode (Int.negSucc n)) = true := by
  rw [encode_int_negSucc]
  simp [intCodeNegative, Nat.bodd]

@[simp]
theorem intCodeMagnitude_encode_ofNat (n : Nat) :
    intCodeMagnitude (encode (Int.ofNat n)) = n := by
  rw [encode_int_ofNat]
  simp [intCodeMagnitude, Nat.bodd, Nat.div2]

@[simp]
theorem intCodeMagnitude_encode_negSucc (n : Nat) :
    intCodeMagnitude (encode (Int.negSucc n)) = n + 1 := by
  rw [encode_int_negSucc]
  simp [intCodeMagnitude, Nat.bodd, Nat.div2]
  simpa [Nat.bit_val] using Nat.bit_div_two true n

@[simp]
theorem intCodeMagnitude_encode (integer : Int) :
    intCodeMagnitude (encode integer) = integer.natAbs := by
  cases integer with
  | ofNat n => exact intCodeMagnitude_encode_ofNat n
  | negSucc n => exact intCodeMagnitude_encode_negSucc n

/-- Negation on encoded integers. -/
def intCodeNegate (code : Nat) : Nat :=
  intCodeOfSignMagnitude (!intCodeNegative code) (intCodeMagnitude code)

/-- Addition on encoded integers. -/
def intCodeAdd (left right : Nat) : Nat :=
  let leftNegative := intCodeNegative left
  let rightNegative := intCodeNegative right
  let leftMagnitude := intCodeMagnitude left
  let rightMagnitude := intCodeMagnitude right
  if leftNegative = rightNegative then
    intCodeOfSignMagnitude leftNegative (leftMagnitude + rightMagnitude)
  else if rightMagnitude ≤ leftMagnitude then
    intCodeOfSignMagnitude leftNegative (leftMagnitude - rightMagnitude)
  else
    intCodeOfSignMagnitude rightNegative (rightMagnitude - leftMagnitude)

/-- Multiplication on encoded integers. -/
def intCodeMultiply (left right : Nat) : Nat :=
  intCodeOfSignMagnitude
    (Bool.xor (intCodeNegative left) (intCodeNegative right))
    (intCodeMagnitude left * intCodeMagnitude right)

/-- Divisibility on encoded integers. -/
def intCodeDivides (divisor dividend : Nat) : Bool :=
  decide (intCodeMagnitude dividend % intCodeMagnitude divisor = 0)

theorem intCodeNegate_primrec : Primrec intCodeNegate := by
  exact intCodeOfSignMagnitude_primrec.comp
    (Primrec.not.comp intCodeNegative_primrec)
    intCodeMagnitude_primrec

theorem intCodeAdd_primrec : Primrec₂ intCodeAdd := by
  change Primrec fun input : Nat × Nat => intCodeAdd input.1 input.2
  let leftNegative : Primrec
      (fun input : Nat × Nat => intCodeNegative input.1) :=
    intCodeNegative_primrec.comp Primrec.fst
  let rightNegative : Primrec
      (fun input : Nat × Nat => intCodeNegative input.2) :=
    intCodeNegative_primrec.comp Primrec.snd
  let leftMagnitude : Primrec
      (fun input : Nat × Nat => intCodeMagnitude input.1) :=
    intCodeMagnitude_primrec.comp Primrec.fst
  let rightMagnitude : Primrec
      (fun input : Nat × Nat => intCodeMagnitude input.2) :=
    intCodeMagnitude_primrec.comp Primrec.snd
  unfold intCodeAdd
  exact Primrec.ite (Primrec.eq.comp leftNegative rightNegative)
    (intCodeOfSignMagnitude_primrec.comp leftNegative
      (Primrec.nat_add.comp leftMagnitude rightMagnitude))
    (Primrec.ite (Primrec.nat_le.comp rightMagnitude leftMagnitude)
      (intCodeOfSignMagnitude_primrec.comp leftNegative
        (Primrec.nat_sub.comp leftMagnitude rightMagnitude))
      (intCodeOfSignMagnitude_primrec.comp rightNegative
        (Primrec.nat_sub.comp rightMagnitude leftMagnitude)))

theorem intCodeMultiply_primrec : Primrec₂ intCodeMultiply := by
  change Primrec fun input : Nat × Nat => intCodeMultiply input.1 input.2
  unfold intCodeMultiply
  exact intCodeOfSignMagnitude_primrec.comp
    ((Primrec.dom_bool₂ Bool.xor).comp
      (intCodeNegative_primrec.comp Primrec.fst)
      (intCodeNegative_primrec.comp Primrec.snd))
    (Primrec.nat_mul.comp
      (intCodeMagnitude_primrec.comp Primrec.fst)
      (intCodeMagnitude_primrec.comp Primrec.snd))

theorem intCodeDivides_primrec : Primrec₂ intCodeDivides := by
  change Primrec fun input : Nat × Nat => intCodeDivides input.1 input.2
  unfold intCodeDivides
  exact (Primrec.eq.comp
    (Primrec.nat_mod.comp
      (intCodeMagnitude_primrec.comp Primrec.snd)
      (intCodeMagnitude_primrec.comp Primrec.fst))
    (Primrec.const 0)).decide

@[simp]
theorem intCodeOfSignMagnitude_false (magnitude : Nat) :
    intCodeOfSignMagnitude false magnitude = 2 * magnitude := by
  cases magnitude <;> simp [intCodeOfSignMagnitude]

theorem intCodeOfSignMagnitude_true {magnitude : Nat} (positive : 0 < magnitude) :
    intCodeOfSignMagnitude true magnitude = 2 * (magnitude - 1) + 1 := by
  simp [intCodeOfSignMagnitude, Nat.ne_of_gt positive]

@[simp]
theorem intCodeNegate_correct (integer : Int) :
    intCodeNegate (encode integer) = encode (-integer) := by
  cases integer with
  | ofNat n =>
      rw [intCodeNegate, intCodeNegative_encode_ofNat,
        intCodeMagnitude_encode_ofNat]
      cases n with
      | zero =>
          simp only [intCodeOfSignMagnitude]
          exact (encode_int_ofNat 0).symm
      | succ n =>
          simp only [intCodeOfSignMagnitude, Nat.succ_ne_zero, ↓reduceIte,
            Bool.not_false, cond_true, Nat.succ_sub_one]
          change 2 * n + 1 = encode (Int.negSucc n)
          exact (encode_int_negSucc n).symm
  | negSucc n =>
      rw [intCodeNegate, intCodeNegative_encode_negSucc,
        intCodeMagnitude_encode_negSucc]
      simp only [intCodeOfSignMagnitude, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, Bool.not_true, cond_false]
      change 2 * (n + 1) = encode (Int.ofNat (n + 1))
      exact (encode_int_ofNat (n + 1)).symm

@[simp]
theorem intCodeAdd_correct (left right : Int) :
    intCodeAdd (encode left) (encode right) = encode (left + right) := by
  cases left with
  | ofNat left =>
      cases right with
      | ofNat right =>
          change intCodeAdd (encode (Int.ofNat left))
            (encode (Int.ofNat right)) = encode (Int.ofNat (left + right))
          rw [intCodeAdd, intCodeNegative_encode_ofNat,
            intCodeNegative_encode_ofNat, intCodeMagnitude_encode_ofNat,
            intCodeMagnitude_encode_ofNat]
          simp only [↓reduceIte, intCodeOfSignMagnitude_false]
          rw [encode_int_ofNat]
      | negSucc right =>
          rw [intCodeAdd, intCodeNegative_encode_ofNat,
            intCodeNegative_encode_negSucc, intCodeMagnitude_encode_ofNat,
            intCodeMagnitude_encode_negSucc]
          simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases h : right + 1 ≤ left
          · rw [if_pos h, intCodeOfSignMagnitude_false,
              Int.ofNat_add_negSucc_of_ge h, encode_int_ofNat]
          · have hlt : left < right + 1 := Nat.lt_of_not_ge h
            have positive : 0 < right + 1 - left := by omega
            rw [if_neg h, intCodeOfSignMagnitude_true positive,
              Int.ofNat_add_negSucc_of_lt hlt, encode_int_negSucc]
            omega
  | negSucc left =>
      cases right with
      | ofNat right =>
          rw [intCodeAdd, intCodeNegative_encode_negSucc,
            intCodeNegative_encode_ofNat, intCodeMagnitude_encode_negSucc,
            intCodeMagnitude_encode_ofNat]
          simp only [Bool.true_eq_false, ↓reduceIte]
          by_cases h : right ≤ left + 1
          · rw [if_pos h]
            by_cases hlt : right < left + 1
            · have positive : 0 < left + 1 - right := by omega
              rw [intCodeOfSignMagnitude_true positive, Int.add_comm,
                Int.ofNat_add_negSucc_of_lt hlt, encode_int_negSucc]
              omega
            · rw [Int.add_comm,
                Int.ofNat_add_negSucc_of_ge (Nat.le_of_not_gt hlt)]
              change intCodeOfSignMagnitude true (left + 1 - right) =
                encode (Int.ofNat (right - (left + 1)))
              rw [encode_int_ofNat]
              have heq : right = left + 1 :=
                Nat.le_antisymm h (Nat.le_of_not_gt hlt)
              simp [heq, intCodeOfSignMagnitude]
          · have hgt : left + 1 < right := Nat.lt_of_not_ge h
            rw [if_neg h, intCodeOfSignMagnitude_false, Int.add_comm,
              Int.ofNat_add_negSucc_of_ge]
            · rw [encode_int_ofNat]
            · omega
      | negSucc right =>
          change intCodeAdd (encode (Int.negSucc left))
            (encode (Int.negSucc right)) =
            encode (Int.negSucc (Nat.succ (left + right)))
          rw [intCodeAdd, intCodeNegative_encode_negSucc,
            intCodeNegative_encode_negSucc, intCodeMagnitude_encode_negSucc,
            intCodeMagnitude_encode_negSucc]
          simp only [↓reduceIte]
          rw [intCodeOfSignMagnitude_true (by omega)]
          rw [encode_int_negSucc]
          omega

@[simp]
theorem intCodeMultiply_correct (left right : Int) :
    intCodeMultiply (encode left) (encode right) = encode (left * right) := by
  cases left with
  | ofNat left =>
      cases right with
      | ofNat right =>
          change intCodeMultiply (encode (Int.ofNat left))
            (encode (Int.ofNat right)) = encode (Int.ofNat (left * right))
          rw [intCodeMultiply, intCodeNegative_encode_ofNat,
            intCodeNegative_encode_ofNat, intCodeMagnitude_encode_ofNat,
            intCodeMagnitude_encode_ofNat]
          simp only [Bool.xor_false, intCodeOfSignMagnitude_false]
          rw [encode_int_ofNat]
      | negSucc right =>
          rw [intCodeMultiply, intCodeNegative_encode_ofNat,
            intCodeNegative_encode_negSucc, intCodeMagnitude_encode_ofNat,
            intCodeMagnitude_encode_negSucc]
          simp only [Bool.xor_true, Bool.not_false]
          cases left with
          | zero =>
              simp only [zero_mul]
              have product_eq :
                  Int.ofNat 0 * Int.negSucc right = Int.ofNat 0 := by
                simp [Int.negSucc_eq]
              rw [product_eq]
              change intCodeOfSignMagnitude true 0 = encode (Int.ofNat 0)
              rw [encode_int_ofNat]
              simp [intCodeOfSignMagnitude]
          | succ left =>
              have positive : 0 < (left + 1) * (right + 1) :=
                Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
              rw [intCodeOfSignMagnitude_true positive]
              have product_eq :
                  Int.ofNat (left + 1) * Int.negSucc right =
                    Int.negSucc ((left + 1) * (right + 1) - 1) := by
                simp [Int.negSucc_eq]
                ring
              rw [product_eq, encode_int_negSucc]
  | negSucc left =>
      cases right with
      | ofNat right =>
          rw [intCodeMultiply, intCodeNegative_encode_negSucc,
            intCodeNegative_encode_ofNat, intCodeMagnitude_encode_negSucc,
            intCodeMagnitude_encode_ofNat]
          simp only [Bool.xor_false]
          cases right with
          | zero =>
              simp only [mul_zero]
              change intCodeOfSignMagnitude true 0 = encode (Int.ofNat 0)
              rw [encode_int_ofNat]
              simp [intCodeOfSignMagnitude]
          | succ right =>
              have positive : 0 < (left + 1) * (right + 1) :=
                Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
              rw [intCodeOfSignMagnitude_true positive]
              have product_eq :
                  Int.negSucc left * Int.ofNat (right + 1) =
                    Int.negSucc ((left + 1) * (right + 1) - 1) := by
                simp [Int.negSucc_eq]
                ring
              rw [product_eq, encode_int_negSucc]
      | negSucc right =>
          rw [intCodeMultiply, intCodeNegative_encode_negSucc,
            intCodeNegative_encode_negSucc, intCodeMagnitude_encode_negSucc,
            intCodeMagnitude_encode_negSucc]
          simp only [Bool.xor_true, Bool.not_true,
            intCodeOfSignMagnitude_false]
          have product_eq :
              Int.negSucc left * Int.negSucc right =
                Int.ofNat ((left + 1) * (right + 1)) := by
            simp [Int.negSucc_eq]
            ring
          rw [product_eq, encode_int_ofNat]

@[simp]
theorem intCodeDivides_correct (divisor dividend : Int) :
    intCodeDivides (encode divisor) (encode dividend) =
      decide (divisor ∣ dividend) := by
  simp only [intCodeDivides, intCodeMagnitude_encode]
  congr 1
  rw [← Int.natAbs_dvd_natAbs, Nat.dvd_iff_mod_eq_zero]

/-- Integer negation is primitive recursive for Mathlib's `Int` encoding. -/
theorem int_negate_primrec : Primrec ((-·) : Int → Int) := by
  apply Primrec.encode_iff.mp
  exact (intCodeNegate_primrec.comp Primrec.encode).of_eq
    intCodeNegate_correct

/-- Integer addition is primitive recursive for Mathlib's `Int` encoding. -/
theorem int_add_primrec : Primrec₂ ((· + ·) : Int → Int → Int) := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeAdd_primrec.comp₂
    (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq intCodeAdd_correct

/-- Integer multiplication is primitive recursive for Mathlib's `Int` encoding. -/
theorem int_multiply_primrec : Primrec₂ ((· * ·) : Int → Int → Int) := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeMultiply_primrec.comp₂
    (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq intCodeMultiply_correct

/-- Integer divisibility is a primitive-recursive relation. -/
theorem int_divides_primrec : PrimrecRel ((· ∣ ·) : Int → Int → Prop) := by
  apply Primrec₂.primrecRel
  exact (intCodeDivides_primrec.comp₂
    (Primrec.encode.comp₂ Primrec₂.left)
    (Primrec.encode.comp₂ Primrec₂.right)).of_eq intCodeDivides_correct

/-- Coercion of naturals to integers is primitive recursive. -/
theorem int_ofNat_primrec : Primrec (Int.ofNat : Nat → Int) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq
    encode_int_ofNat

/-- Truncating an integer to a natural number is primitive recursive. -/
theorem int_toNat_primrec : Primrec Int.toNat := by
  exact (Primrec.cond
    (intCodeNegative_primrec.comp Primrec.encode)
    (Primrec.const 0)
    (intCodeMagnitude_primrec.comp Primrec.encode)).of_eq fun integer => by
      cases integer with
      | ofNat n =>
          rw [intCodeNegative_encode_ofNat,
            intCodeMagnitude_encode_ofNat]
          rfl
      | negSucc n =>
          rw [intCodeNegative_encode_negSucc]
          rfl

/-- Divide an encoded integer by a natural divisor.  For a positive divisor,
the odd code `2*n+1` of `-(n+1)` maps to the odd code for
`-((n / divisor) + 1)`, exactly Lean's Euclidean integer quotient. -/
def intCodeEdivNat (code divisor : Nat) : Nat :=
  if divisor = 0 then
    0
  else bif intCodeNegative code then
    2 * (code.div2 / divisor) + 1
  else
    2 * (code.div2 / divisor)

theorem intCodeEdivNat_primrec : Primrec₂ intCodeEdivNat := by
  change Primrec fun input : Nat × Nat =>
    intCodeEdivNat input.1 input.2
  let quotient : Nat × Nat → Nat := fun input =>
    input.1.div2 / input.2
  have quotientPrimrec : Primrec quotient :=
    Primrec.nat_div.comp
      (Primrec.nat_div2.comp Primrec.fst) Primrec.snd
  have positive : Primrec fun input : Nat × Nat =>
      2 * quotient input :=
    Primrec.nat_mul.comp (Primrec.const 2) quotientPrimrec
  have negative : Primrec fun input : Nat × Nat =>
      2 * quotient input + 1 :=
    Primrec.nat_add.comp positive (Primrec.const 1)
  simpa only [intCodeEdivNat, quotient] using (Primrec.ite
    (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const 0)
    (Primrec.cond
      (intCodeNegative_primrec.comp Primrec.fst)
      negative positive))

@[simp]
theorem intCodeEdivNat_correct (integer : Int) (divisor : Nat) :
    intCodeEdivNat (encode integer) divisor =
      encode (integer / (divisor : Int)) := by
  cases divisor with
  | zero =>
      change intCodeEdivNat (encode integer) 0 =
        encode (integer / (0 : Int))
      rw [Int.ediv_zero]
      change intCodeEdivNat (encode integer) 0 = encode (Int.ofNat 0)
      rw [show intCodeEdivNat (encode integer) 0 = 0 by
        simp [intCodeEdivNat], encode_int_ofNat]
  | succ divisor =>
      cases integer with
      | ofNat value =>
          change intCodeEdivNat (encode (Int.ofNat value)) (divisor + 1) =
            encode (Int.ofNat (value / (divisor + 1)))
          rw [encode_int_ofNat, encode_int_ofNat]
          simp [intCodeEdivNat, intCodeNegative, Nat.bodd,
            Nat.div2_bit0]
      | negSucc value =>
          change intCodeEdivNat (encode (Int.negSucc value)) (divisor + 1) =
            encode (Int.negSucc (value / (divisor + 1)))
          rw [encode_int_negSucc, encode_int_negSucc]
          simp [intCodeEdivNat, intCodeNegative, Nat.bodd]

/-- Euclidean division of an integer by a natural divisor is primitive
recursive (including Lean's total zero-divisor case). -/
theorem int_edivNat_primrec :
    Primrec₂ fun integer : Int => fun divisor : Nat =>
      integer / (divisor : Int) := by
  apply Primrec₂.encode_iff.mp
  exact (intCodeEdivNat_primrec.comp₂
    (Primrec.encode.comp₂ Primrec₂.left)
    Primrec₂.right).of_eq intCodeEdivNat_correct

/-- Integer subtraction is primitive recursive. -/
theorem int_subtract_primrec : Primrec₂ ((· - ·) : Int → Int → Int) := by
  simpa only [sub_eq_add_neg] using
    int_add_primrec.comp₂ Primrec₂.left
      (int_negate_primrec.comp₂ Primrec₂.right)

/-- Coordinatewise subtraction of cells is primitive recursive. -/
theorem cell_sub_primrec : Primrec₂ Cell.sub := by
  unfold Cell.sub
  exact Primrec₂.pair.comp₂
    (int_subtract_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.fst.comp₂ Primrec₂.right))
    (int_subtract_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right))

/-- Coordinatewise addition of cells is primitive recursive. -/
theorem cell_add_primrec : Primrec₂ Cell.add := by
  unfold Cell.add
  exact Primrec₂.pair.comp₂
    (int_add_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.fst.comp₂ Primrec₂.right))
    (int_add_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right))

/-- Integer scaling of cells is primitive recursive. -/
theorem cell_scale_primrec : Primrec₂ Cell.scale := by
  unfold Cell.scale
  exact Primrec₂.pair.comp₂
    (int_multiply_primrec.comp₂ Primrec₂.left
      (Primrec.fst.comp₂ Primrec₂.right))
    (int_multiply_primrec.comp₂ Primrec₂.left
      (Primrec.snd.comp₂ Primrec₂.right))

/-- The action of every square-grid symmetry on cells is primitive recursive. -/
theorem squareSymmetry_act_primrec : Primrec₂ SquareSymmetry.act := by
  change Primrec fun input : SquareSymmetry × Cell =>
    SquareSymmetry.act input.1 input.2
  let x : Primrec (fun input : SquareSymmetry × Cell => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  let y : Primrec (fun input : SquareSymmetry × Cell => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  let negX := int_negate_primrec.comp x
  let negY := int_negate_primrec.comp y
  let is (symmetry : SquareSymmetry) : PrimrecPred (fun input :
      SquareSymmetry × Cell => input.1 = symmetry) :=
    Primrec.eq.comp Primrec.fst (Primrec.const symmetry)
  exact (Primrec.ite (is .identity) (Primrec.pair x y)
    (Primrec.ite (is .rotate90) (Primrec.pair negY x)
    (Primrec.ite (is .rotate180) (Primrec.pair negX negY)
    (Primrec.ite (is .rotate270) (Primrec.pair y negX)
    (Primrec.ite (is .reflectX) (Primrec.pair x negY)
    (Primrec.ite (is .reflectDiagonal) (Primrec.pair y x)
    (Primrec.ite (is .reflectY) (Primrec.pair negX y)
      (Primrec.pair negY negX)))))))).of_eq fun input => by
        rcases input with ⟨symmetry, cell⟩
        cases symmetry <;> rfl

/-- Nonnegativity of integers is primitive recursive. -/
theorem int_nonnegative_primrec : PrimrecPred fun integer : Int => 0 ≤ integer := by
  apply Primrec.primrecPred
  apply (Primrec.not.comp
    (intCodeNegative_primrec.comp Primrec.encode)).of_eq
  intro integer
  apply Bool.eq_iff_iff.mpr
  cases integer with
  | ofNat n => rw [intCodeNegative_encode_ofNat]; simp
  | negSucc n => rw [intCodeNegative_encode_negSucc]; simp

/-- Integer order is a primitive-recursive relation. -/
theorem int_le_primrec : PrimrecRel ((· ≤ ·) : Int → Int → Prop) := by
  have nonnegativeDifference : PrimrecRel fun left right : Int =>
      0 ≤ right - left :=
    (int_nonnegative_primrec.comp
      (int_subtract_primrec.comp Primrec.snd Primrec.fst)).primrecRel
  exact nonnegativeDifference.of_eq fun _ _ => by omega

/-- Strict integer order is a primitive-recursive relation. -/
theorem int_lt_primrec : PrimrecRel ((· < ·) : Int → Int → Prop) := by
  exact int_le_primrec.swap.not.of_eq fun _ _ => not_le

/-- The product representation defining `PeriodicRegion`'s encoding is
primitive recursive. -/
theorem periodicRegion_equivData_primrec :
    Primrec PeriodicRegion.equivData := by
  exact Primrec.of_equiv

theorem periodicRegion_motif_primrec :
    Primrec PeriodicRegion.motif := by
  exact (Primrec.fst.comp periodicRegion_equivData_primrec).of_eq
    (fun _ => rfl)

theorem periodicRegion_period₁_primrec :
    Primrec PeriodicRegion.period₁ := by
  exact (Primrec.fst.comp
    (Primrec.snd.comp periodicRegion_equivData_primrec)).of_eq
      (fun _ => rfl)

theorem periodicRegion_period₂_primrec :
    Primrec PeriodicRegion.period₂ := by
  exact (Primrec.snd.comp
    (Primrec.snd.comp periodicRegion_equivData_primrec)).of_eq
      (fun _ => rfl)

theorem periodicRegion_determinant_primrec :
    Primrec PeriodicRegion.determinant := by
  unfold PeriodicRegion.determinant
  exact int_subtract_primrec.comp
    (int_multiply_primrec.comp
      (Primrec.fst.comp periodicRegion_period₁_primrec)
      (Primrec.snd.comp periodicRegion_period₂_primrec))
    (int_multiply_primrec.comp
      (Primrec.snd.comp periodicRegion_period₁_primrec)
      (Primrec.fst.comp periodicRegion_period₂_primrec))

theorem periodicRegion_firstNumerator_primrec :
    Primrec₂ PeriodicRegion.firstNumerator := by
  unfold PeriodicRegion.firstNumerator
  exact int_subtract_primrec.comp₂
    (int_multiply_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      ((Primrec.snd.comp periodicRegion_period₂_primrec).comp₂
        Primrec₂.left))
    (int_multiply_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.right)
      ((Primrec.fst.comp periodicRegion_period₂_primrec).comp₂
        Primrec₂.left))

theorem periodicRegion_secondNumerator_primrec :
    Primrec₂ PeriodicRegion.secondNumerator := by
  unfold PeriodicRegion.secondNumerator
  exact int_subtract_primrec.comp₂
    (int_multiply_primrec.comp₂
      ((Primrec.fst.comp periodicRegion_period₁_primrec).comp₂
        Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.right))
    (int_multiply_primrec.comp₂
      ((Primrec.snd.comp periodicRegion_period₁_primrec).comp₂
        Primrec₂.left)
      (Primrec.fst.comp₂ Primrec₂.right))

/-- The Cramer-divisibility test underlying lattice membership is a
primitive-recursive relation. -/
theorem periodicRegion_latticeArithmetic_primrec :
    PrimrecRel fun (periodicRegion : PeriodicRegion) (cell : Cell) =>
      periodicRegion.determinant ∣ periodicRegion.firstNumerator cell ∧
        periodicRegion.determinant ∣ periodicRegion.secondNumerator cell := by
  exact (int_divides_primrec.comp₂
    (periodicRegion_determinant_primrec.comp₂ Primrec₂.left)
    periodicRegion_firstNumerator_primrec).and
      (int_divides_primrec.comp₂
        (periodicRegion_determinant_primrec.comp₂ Primrec₂.left)
        periodicRegion_secondNumerator_primrec)

/-- Finite arithmetic form of membership in a periodic region. -/
def PeriodicRegionArithmeticContains
    (periodicRegion : PeriodicRegion) (cell : Cell) : Prop :=
  ∃ base ∈ periodicRegion.motif,
    periodicRegion.determinant ∣
        periodicRegion.firstNumerator (Cell.sub cell base) ∧
      periodicRegion.determinant ∣
        periodicRegion.secondNumerator (Cell.sub cell base)

theorem periodicRegion_arithmeticContains_primrec :
    PrimrecRel PeriodicRegionArithmeticContains := by
  let baseRelation : PrimrecRel fun base (input : PeriodicRegion × Cell) =>
      input.1.determinant ∣
          input.1.firstNumerator (Cell.sub input.2 base) ∧
        input.1.determinant ∣
          input.1.secondNumerator (Cell.sub input.2 base) :=
    periodicRegion_latticeArithmetic_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (cell_sub_primrec.comp₂
        (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left)
  exact ((baseRelation.exists_mem_list.comp
    (periodicRegion_motif_primrec.comp Primrec.fst)
    Primrec.id).primrecRel).of_eq (fun _ _ => Iff.rfl)

theorem periodicRegion_arithmeticContains_iff_contains
    (periodicRegion : PeriodicRegion) (cell : Cell) :
    PeriodicRegionArithmeticContains periodicRegion cell ↔
      periodicRegion.contains cell = true := by
  simp [PeriodicRegionArithmeticContains, PeriodicRegion.contains,
    PeriodicRegion.latticeContains, Cell.sub]

theorem periodicRegion_isFullRank_primrec :
    PrimrecPred PeriodicRegion.IsFullRank := by
  unfold PeriodicRegion.IsFullRank
  exact (Primrec.eq.comp periodicRegion_determinant_primrec
    (Primrec.const 0)).not

/-- Valid membership in the represented 2D periodic region is a
primitive-recursive relation. -/
theorem periodicRegion_validMembership_primrec :
    PrimrecRel fun (periodicRegion : PeriodicRegion) (cell : Cell) =>
      periodicRegion.IsFullRank ∧ cell ∈ periodicRegion.carrier := by
  have fullRankRelation : PrimrecRel fun (periodicRegion : PeriodicRegion)
      (_ : Cell) =>
      periodicRegion.IsFullRank :=
    (periodicRegion_isFullRank_primrec.comp Primrec.fst).primrecRel
  have conjunctionRelation : PrimrecRel fun periodicRegion cell =>
      periodicRegion.IsFullRank ∧
        PeriodicRegionArithmeticContains periodicRegion cell :=
    fullRankRelation.and periodicRegion_arithmeticContains_primrec
  apply PrimrecRel.of_eq conjunctionRelation
  intro periodicRegion cell
  rw [periodicRegion_arithmeticContains_iff_contains]
  constructor
  · rintro ⟨fullRank, contains⟩
    exact ⟨fullRank,
      (periodicRegion.contains_eq_true_iff fullRank cell).mp contains⟩
  · rintro ⟨fullRank, member⟩
    exact ⟨fullRank,
      (periodicRegion.contains_eq_true_iff fullRank cell).mpr member⟩

/-- The executable valid-membership checker is primitive recursive. -/
theorem periodicRegion_validContains_primrec :
    Primrec₂ PeriodicRegion.validContains := by
  apply (PrimrecRel.decide periodicRegion_validMembership_primrec).of_eq
  intro periodicRegion cell
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,
    periodicRegion.validContains_eq_true_iff]

/-- The product representation defining `PeriodicStrip`'s encoding is
primitive recursive. -/
theorem periodicStrip_equivData_primrec :
    Primrec PeriodicStrip.equivData := by
  exact Primrec.of_equiv

theorem periodicStrip_width_primrec : Primrec PeriodicStrip.width := by
  exact (Primrec.fst.comp periodicStrip_equivData_primrec).of_eq
    (fun _ => rfl)

theorem periodicStrip_period_primrec : Primrec PeriodicStrip.period := by
  exact (Primrec.fst.comp
    (Primrec.snd.comp periodicStrip_equivData_primrec)).of_eq
      (fun _ => rfl)

theorem periodicStrip_motif_primrec : Primrec PeriodicStrip.motif := by
  exact (Primrec.snd.comp
    (Primrec.snd.comp periodicStrip_equivData_primrec)).of_eq
      (fun _ => rfl)

/-- Membership in a strip's chosen fundamental domain is a
primitive-recursive relation. -/
theorem periodicStrip_inFundamentalDomain_primrec :
    PrimrecRel PeriodicStrip.InFundamentalDomain := by
  have xNonnegative : PrimrecRel fun (_ : PeriodicStrip) (cell : Cell) =>
      0 ≤ cell.1 :=
    (int_nonnegative_primrec.comp
      (Primrec.fst.comp Primrec.snd)).primrecRel
  have xBelowPeriod : PrimrecRel fun (periodicStrip : PeriodicStrip)
      (cell : Cell) => cell.1 < (periodicStrip.period : Int) :=
    int_lt_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      ((int_ofNat_primrec.comp periodicStrip_period_primrec).comp₂
        Primrec₂.left)
  have yNonnegative : PrimrecRel fun (_ : PeriodicStrip) (cell : Cell) =>
      0 ≤ cell.2 :=
    (int_nonnegative_primrec.comp
      (Primrec.snd.comp Primrec.snd)).primrecRel
  have yBelowWidth : PrimrecRel fun (periodicStrip : PeriodicStrip)
      (cell : Cell) => cell.2 < (periodicStrip.width : Int) :=
    int_lt_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.right)
      ((int_ofNat_primrec.comp periodicStrip_width_primrec).comp₂
        Primrec₂.left)
  have constraints : PrimrecRel fun (periodicStrip : PeriodicStrip)
      (cell : Cell) =>
      0 ≤ cell.1 ∧ cell.1 < (periodicStrip.period : Int) ∧
        0 ≤ cell.2 ∧ cell.2 < (periodicStrip.width : Int) :=
    xNonnegative.and (xBelowPeriod.and (yNonnegative.and yBelowWidth))
  exact PrimrecRel.of_eq constraints fun _ _ => Iff.rfl

/-- Well-formedness of a periodic-strip presentation is primitive recursive. -/
theorem periodicStrip_isWellFormed_primrec :
    PrimrecPred PeriodicStrip.IsWellFormed := by
  have widthPositive : PrimrecPred fun periodicStrip : PeriodicStrip =>
      0 < periodicStrip.width :=
    Primrec.nat_lt.comp (Primrec.const 0) periodicStrip_width_primrec
  have periodPositive : PrimrecPred fun periodicStrip : PeriodicStrip =>
      0 < periodicStrip.period :=
    Primrec.nat_lt.comp (Primrec.const 0) periodicStrip_period_primrec
  have motifInDomain : PrimrecPred fun periodicStrip : PeriodicStrip =>
      ∀ cell ∈ periodicStrip.motif,
        periodicStrip.InFundamentalDomain cell :=
    periodicStrip_inFundamentalDomain_primrec.swap.forall_mem_list.comp
      periodicStrip_motif_primrec Primrec.id
  exact (widthPositive.and (periodPositive.and motifInDomain)).of_eq
    (fun _ => by simp [PeriodicStrip.IsWellFormed])

/-- The executable well-formedness checker is primitive recursive. -/
theorem periodicStrip_wellFormed_primrec :
    Primrec PeriodicStrip.wellFormed := by
  apply (PrimrecPred.decide periodicStrip_isWellFormed_primrec).of_eq
  intro periodicStrip
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, periodicStrip.wellFormed_eq_true_iff]

/-- Membership in the infinite carrier represented by a periodic strip is a
primitive-recursive relation. -/
theorem periodicStrip_membership_primrec :
    PrimrecRel fun (periodicStrip : PeriodicStrip) (cell : Cell) =>
      cell ∈ periodicStrip.carrier := by
  have yNonnegative : PrimrecRel fun (_ : PeriodicStrip) (cell : Cell) =>
      0 ≤ cell.2 :=
    (int_nonnegative_primrec.comp
      (Primrec.snd.comp Primrec.snd)).primrecRel
  have yBelowWidth : PrimrecRel fun (periodicStrip : PeriodicStrip)
      (cell : Cell) => cell.2 < (periodicStrip.width : Int) :=
    int_lt_primrec.comp₂
      (Primrec.snd.comp₂ Primrec₂.right)
      ((int_ofNat_primrec.comp periodicStrip_width_primrec).comp₂
        Primrec₂.left)
  let baseRelation : PrimrecRel fun (base : Cell)
      (input : PeriodicStrip × Cell) =>
      base.2 = input.2.2 ∧
        (input.1.period : Int) ∣ input.2.1 - base.1 :=
    (Primrec.eq.comp₂
      (Primrec.snd.comp₂ Primrec₂.left)
      ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.right)).and
    (int_divides_primrec.comp₂
      ((int_ofNat_primrec.comp periodicStrip_period_primrec).comp₂
        (Primrec.fst.comp₂ Primrec₂.right))
      (int_subtract_primrec.comp₂
        ((Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.right)
        (Primrec.fst.comp₂ Primrec₂.left)))
  have motifWitness : PrimrecRel fun (periodicStrip : PeriodicStrip)
      (cell : Cell) => ∃ base ∈ periodicStrip.motif,
        base.2 = cell.2 ∧
          (periodicStrip.period : Int) ∣ cell.1 - base.1 :=
    ((baseRelation.exists_mem_list.comp
      (periodicStrip_motif_primrec.comp Primrec.fst)
      Primrec.id).primrecRel).of_eq (fun _ _ => Iff.rfl)
  have arithmeticMembership : PrimrecRel fun
      (periodicStrip : PeriodicStrip) (cell : Cell) =>
      0 ≤ cell.2 ∧ cell.2 < (periodicStrip.width : Int) ∧
        ∃ base ∈ periodicStrip.motif,
          base.2 = cell.2 ∧
            (periodicStrip.period : Int) ∣ cell.1 - base.1 :=
    yNonnegative.and (yBelowWidth.and motifWitness)
  exact arithmeticMembership.of_eq fun periodicStrip cell =>
    (periodicStrip.mem_carrier_iff cell).symm

/-- The executable periodic-strip membership checker is primitive recursive. -/
theorem periodicStrip_contains_primrec :
    Primrec₂ PeriodicStrip.contains := by
  apply (PrimrecRel.decide periodicStrip_membership_primrec).of_eq
  intro periodicStrip cell
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, periodicStrip.contains_eq_true_iff]

end LeanTrominoes.Computability
