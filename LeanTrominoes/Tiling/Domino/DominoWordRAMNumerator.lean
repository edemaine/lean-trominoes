/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMNumeratorEquality

/-! # Complete checked multiword divisibility and quotient parity test -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Numerator
open ComplexityAbstract.RAM

structure Input (g : Geometry) (source : ℕ → ℕ) (z b : ℤ) : Prop where
  positive : 0< g.precision
  numerator_bits : ∀ j< g.precision, source (g.numerator+j)≤1
  denominator_bits : ∀ j< g.precision, source (g.determinant+j)≤1
  twice_bits : ∀ j< g.precision, source (g.twice+j)≤1
  zero : ∀ j< g.precision, source (g.zero+j)=0
  remainder_zero : ∀ j< g.precision, source (g.remainder+j)=0
  numerator_fits : Fits g.precision z
  numerator_value : (value source g.numerator g.precision : ℤ)=z%(2^g.precision : ℤ)
  determinant_value : value source g.determinant g.precision=b.natAbs
  twice_value : value source g.twice g.precision=2*b.natAbs
  nonzero : b≠0
  guard : 4*b.natAbs≤2^g.precision

structure Result (g : Geometry) (source : ℕ → ℕ) (z b : ℤ) (result : Data) : Prop where
  controls : Controls g result
  valid : 0< result.1 G.valid ↔ b∣z
  parity_bit : result.1 G.parity≤1
  parity : result.1 G.parity=1 ↔ z.natAbs%(2*b.natAbs)=b.natAbs
  frame : ∀ address, (address< g.absolute ∨ g.absolute+g.precision≤address) →
    (address< g.remainder ∨ g.remainder+g.precision≤address) →
    (address< g.difference ∨ g.difference+g.precision≤address) → result.2 address=source address

theorem Result.quotient_parity {g : Geometry} {source : ℕ → ℕ} {z b : ℤ} {result : Data}
    (h : Result g source z b result) (nonzero : b≠0) (divisible : b∣z) :
    (z/b)%2=(result.1 G.parity : ℤ) := by
  rw [quotient_parity_natAbs z b divisible]
  have positive : 0< b.natAbs := Int.natAbs_pos.mpr nonzero
  rcases (divisible_iff_unsigned_remainder z b).mp divisible with zero | one
  · have flag : result.1 G.parity=0 := by
      have different : result.1 G.parity≠1 := by
        intro equal
        have same := h.parity.mp equal
        omega
      have bound := h.parity_bit
      omega
    simp [zero,flag]
  · have flag := h.parity.mpr one
    rw [one,flag,Nat.div_self positive]

theorem program_exec {w : ℕ} (g : Geometry) (data : Data) (z b : ℤ)
    (width : Widths g w) (controls : Controls g data) (input : Input g data.2 z b) :
    ∃ result cost, NaturalData.Exec w program data result cost ∧
      cost≤29*g.precision^2+65*g.precision+55 ∧ Result g data.2 z b result := by
  obtain ⟨absolute,absoluteCost,absoluteRun,absoluteBound,absoluteResult⟩ :=
    absolute_exec g data width controls input.positive input.numerator_bits input.zero
  have original (slot : Fin 7) (different : slot≠4) (j : ℕ) (within : j< g.precision) :
      absolute.2 (g.base slot+j)=data.2 (g.base slot+j) :=
    absoluteResult.frame _ (g.outside slot 4 different j within)
  have absoluteValue : value absolute.2 g.absolute g.precision=z.natAbs := by
    rw [absoluteResult.magnitude]
    exact twos_complement_magnitude data.2 g.numerator g.precision z input.positive
      input.numerator_bits input.numerator_fits input.numerator_value
  have twiceValue : value absolute.2 g.twice g.precision=2*b.natAbs := by
    rw [value_congr (fun j hj => original 3 (by decide) j hj)]
    exact input.twice_value
  have denominatorPositive : 0< b.natAbs := Int.natAbs_pos.mpr input.nonzero
  obtain ⟨remainder,remainderCost,remainderRun,remainderBound,remainderResult⟩ :=
    remainder_exec g absolute width absoluteResult.controls absoluteResult.bits
      (fun j hj => by rw [original 3 (by decide) j hj]; exact input.twice_bits j hj)
      (by rw [twiceValue]; omega) (by rw [twiceValue]; have guard := input.guard; omega)
      (fun j hj => by rw [original 5 (by decide) j hj]; exact input.remainder_zero j hj)
  have remainderOriginal (slot : Fin 7) (notR : slot≠5) (notD : slot≠6) (notA : slot≠4)
      (j : ℕ) (within : j< g.precision) : remainder.2 (g.base slot+j)=data.2 (g.base slot+j) := by
    rw [remainderResult.frame _ (g.outside slot 5 notR j within) (g.outside slot 6 notD j within)]
    exact original slot notA j within
  have remainderValue : value remainder.2 g.remainder g.precision=z.natAbs%(2*b.natAbs) := by
    rw [remainderResult.remainder_value,absoluteValue,twiceValue]
  have zeroValue : value remainder.2 g.zero g.precision=0 := by
    unfold value
    apply Finset.sum_eq_zero
    intro j hj
    rw [remainderOriginal 1 (by decide) (by decide) (by decide) j (Finset.mem_range.mp hj),
      input.zero j (Finset.mem_range.mp hj),zero_mul]
  have determinantValue : value remainder.2 g.determinant g.precision=b.natAbs := by
    rw [value_congr (fun j hj => remainderOriginal 2 (by decide) (by decide) (by decide) j hj)]
    exact input.determinant_value
  obtain ⟨zero,zeroCost,zeroRun,zeroBound,zeroResult⟩ := zero_exec g remainder width remainderResult.controls
    remainderResult.bits (fun j hj => by
      rw [remainderOriginal 1 (by decide) (by decide) (by decide) j hj,input.zero j hj]; omega)
  obtain ⟨parity,parityCost,parityRun,parityBound,parityResult⟩ := parity_exec g zero width zeroResult.controls
    (by rw [zeroResult.memory]; exact remainderResult.bits)
    (fun j hj => by rw [zeroResult.memory,remainderOriginal 2 (by decide) (by decide) (by decide) j hj]; exact input.denominator_bits j hj)
  have saved : parity.1 G.isZero=zero.1 G.isZero := by
    have equal := parityRun.register_eq parity_preserves_zero
    simpa only [NaturalData.word,Int.natCast_inj] using equal
  have zeroBit := zeroResult.bounded
  have parityBit := parityResult.bounded
  have flagSum : parity.1 G.isZero+parity.1 G.parity≤2 := by rw [saved]; omega
  have combineFits : Fits w (parity.1 G.isZero+parity.1 G.parity : ℕ) := by
    refine ⟨width.small.1,?_,lt_of_le_of_lt (by exact_mod_cast show parity.1 G.isZero+parity.1 G.parity≤3 by omega) width.small.2.2⟩
    exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)
  have combined := NaturalData.add_exec parity G.valid G.isZero G.parity combineFits
  have full := absoluteRun.seq (remainderRun.seq (zeroRun.seq (parityRun.seq combined)))
  refine ⟨_,absoluteCost+(remainderCost+(zeroCost+(parityCost+1))),full,by omega,?_⟩
  have parityEqual : parity.1 G.parity=1 ↔ z.natAbs%(2*b.natAbs)=b.natAbs := by
    rw [parityResult.equal,zeroResult.memory,remainderValue,determinantValue]
  have zeroEqual : parity.1 G.isZero=1 ↔ z.natAbs%(2*b.natAbs)=0 := by
    rw [saved,zeroResult.equal,remainderValue,zeroValue]
  constructor
  · apply parityResult.controls.after combined
    intro reg high low
    change reg≠G.valid
    intro same
    have equal := congrArg Fin.val same
    change reg.val=52 at equal
    omega
  · change (0<parity.1 G.isZero+parity.1 G.parity ↔ b∣z)
    rw [divisible_iff_unsigned_remainder]
    have zb := zeroResult.bounded
    have pb := parityResult.bounded
    rw [←saved] at zb
    rw [←zeroEqual,←parityEqual]
    omega
  · change parity.1 G.parity≤1
    exact parityResult.bounded
  · change (parity.1 G.parity=1 ↔ _)
    exact parityEqual
  · intro address outsideA outsideR outsideD
    change parity.2 address=data.2 address
    rw [parityResult.memory,zeroResult.memory,remainderResult.frame address outsideR outsideD,
      absoluteResult.frame address outsideA]

end LeanTrominoes.Domino.WordRAM.Binary.Numerator
