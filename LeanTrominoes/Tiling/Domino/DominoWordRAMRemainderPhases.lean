/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainderRead

/-! # Arithmetic and memory guarantees for each remainder phase -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM

structure Widths (g : Geometry) (w : ℕ) : Prop where
  small : Fits w (3:ℕ)
  numerator : Fits w (g.numerator+g.count : ℕ)
  denominator : Fits w (g.denominator+g.precision : ℕ)
  remainder : Fits w (g.remainder+g.precision : ℕ)
  difference : Fits w (g.difference+g.precision : ℕ)
  precision : Fits w g.precision
  count : Fits w g.count

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem Widths.one {g : Geometry} {w : ℕ} (h : Widths g w) : Fits w (1:ℕ) := fits_le h.small (by omega)

/-- Result of bringing the next numerator bit into the low end of the
remainder. Its high carry is zero by the denominator precision bound. -/
theorem shifted_phase {w : ℕ} (g : Geometry) (source : ℕ → ℕ) (position : ℕ) (data : WideData)
    (input : Input g source) (width : Widths g w) (within : position< g.count)
    (controls : Controls g position data) (memory : MemoryRepresents g source (position+1) data)
    (bit : data.1 R.bit=source (g.numerator+position)) :
    ∃ result : Data, NaturalData.Exec w shifted data (extend result (upper data)) (7*g.precision+7) ∧
      Controls g position (extend result (upper data)) ∧
      Sources g source (extend result (upper data)) ∧
      (∀ j< g.precision, result.2 (g.remainder+j)≤1) ∧
      value result.2 g.remainder g.precision=2*value data.2 g.remainder g.precision+source (g.numerator+position) := by
  obtain ⟨result,run,correct⟩ := shifted_exec data g.remainder g.precision controls.remainder controls.precision
    (by rw [bit]; exact input.numerator_bits position within) memory.remainder_bits width.one width.remainder width.precision
  have oldBound : value data.2 g.remainder g.precision<value source g.denominator g.precision := by
    rw [memory.result]
    exact Nat.mod_lt _ input.denominator_positive
  have bitBound := input.numerator_bits position within
  have nextBound : 2*value data.2 g.remainder g.precision+data.1 R.bit<2^g.precision := by
    rw [bit]
    nlinarith only [oldBound,bitBound,input.denominator_small]
  have carryZero : result.1 Reg.carry=0 := by
    by_contra nonzero
    have positive : 1≤result.1 Reg.carry := by omega
    have scaled := Nat.mul_le_mul_right (2^g.precision) positive
    have equation := correct.result
    nlinarith only [scaled,nextBound,equation,Nat.zero_le (value result.2 g.remainder g.precision)]
  have frame : ∀ address, (address< g.remainder ∨ g.remainder+g.precision≤address) →
      (extend result (upper data)).2 address=data.2 address := correct.frame
  refine ⟨result,run,controls.extend result,memory.sources.remainder_write frame,correct.output_bits,?_⟩
  have equation := correct.result
  rw [carryZero,zero_mul,add_zero,bit] at equation
  exact equation

structure Subtracted (g : Geometry) (source : ℕ → ℕ) (position next : ℕ) (data : WideData) : Prop where
  controls : Controls g position data
  sources : Sources g source data
  remainder_bits : ∀ j< g.precision, data.2 (g.remainder+j)≤1
  difference_bits : ∀ j< g.precision, data.2 (g.difference+j)≤1
  remainder_value : value data.2 g.remainder g.precision=next
  borrow : data.1 (low Reg.carry)≤1
  result : value data.2 g.difference g.precision+value source g.denominator g.precision=
    next+data.1 (low Reg.carry)*2^g.precision

theorem subtracted_phase {w : ℕ} (g : Geometry) (source : ℕ → ℕ) (position next : ℕ) (data : WideData)
    (input : Input g source) (width : Widths g w)
    (controls : Controls g position data) (sources : Sources g source data)
    (bits : ∀ j< g.precision, data.2 (g.remainder+j)≤1)
    (valueEq : value data.2 g.remainder g.precision=next) :
    ∃ result : Data, NaturalData.Exec w subtracted data (extend result (upper data)) (15*g.precision+10) ∧
      Subtracted g source position next (extend result (upper data)) := by
  obtain ⟨result,run,correct⟩ := subtracted_exec g.borrowLayout data controls.remainder controls.denominator controls.difference controls.precision
    bits (fun j hj => by change data.2 (g.denominator+j)≤1; rw [sources.denominator j hj]; exact input.denominator_bits j hj)
    width.small width.remainder width.denominator width.difference width.precision
  have frame : ∀ address, (address< g.difference ∨ g.difference+g.precision≤address) →
      (extend result (upper data)).2 address=data.2 address := correct.frame
  have remainderEq : value result.2 g.remainder g.precision=value data.2 g.remainder g.precision :=
    g.value_preserved 2 3 (by decide) data.2 result.2 correct.frame
  have denominatorEq : value data.2 g.denominator g.precision=value source g.denominator g.precision :=
    value_congr sources.denominator
  refine ⟨result,run,?_⟩
  constructor
  · exact controls.extend result
  · exact sources.difference_write frame
  · intro j hj
    rw [frame _ (g.outside 2 3 (by decide) j hj)]
    exact bits j hj
  · exact correct.output_bits
  · exact remainderEq.trans valueEq
  · change result.1 Reg.carry≤1
    exact correct.carry
  · change value result.2 g.difference g.precision+value source g.denominator g.precision=
      next+result.1 Reg.carry*2^g.precision
    have equation := correct.result
    change value result.2 g.difference g.precision+value data.2 g.denominator g.precision=
      value data.2 g.remainder g.precision+result.1 Reg.carry*2^g.precision at equation
    rw [denominatorEq,valueEq] at equation
    exact equation

end LeanTrominoes.Domino.WordRAM.Binary.Remainder
