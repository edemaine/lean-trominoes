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

end LeanTrominoes.Computability
