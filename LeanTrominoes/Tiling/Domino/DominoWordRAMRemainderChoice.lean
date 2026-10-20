/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainderPhases

/-! # The final-borrow guard implements remainder reduction -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM

private theorem zero_fits {g : Geometry} {w : ℕ} (width : Widths g w) : Fits w (0:ℕ) := by
  refine ⟨width.small.1,?_,?_⟩
  · exact neg_nonpos.mpr (by positivity)
  · exact lt_of_le_of_lt (by norm_num : (0:ℤ)≤3) width.small.2.2

theorem accept_phase {w : ℕ} (g : Geometry) (source : ℕ → ℕ) (position next : ℕ) (data : WideData)
    (width : Widths g w) (h : Subtracted g source position next data) :
    ∃ result cost, NaturalData.Exec w accept data result cost ∧ cost≤7*g.precision+8 ∧
      Controls g position result ∧ Sources g source result ∧
      (∀ j< g.precision, result.2 (g.remainder+j)≤1) ∧
      value result.2 g.remainder g.precision=
        if value source g.denominator g.precision≤next then next-value source g.denominator g.precision else next := by
  have test := borrow_zero_iff next (value source g.denominator g.precision)
    (value data.2 g.difference g.precision) (data.1 (low Reg.carry)) g.precision
    (value_lt data.2 g.difference g.precision h.difference_bits) h.borrow h.result
  by_cases zero : data.1 (low Reg.carry)=0
  · have ordered := test.mp zero
    obtain ⟨result,run,correct⟩ := accepted_exec g.copyLayout data h.controls.difference h.controls.remainder
      h.controls.precision h.difference_bits width.one width.difference width.remainder width.precision
    have condition : (Structured.Condition.eq (low Reg.carry) R.zero).Holds data.word := by
      change (data.1 (low Reg.carry) : ℤ)=(data.1 R.zero : ℤ)
      rw [zero,h.controls.zero]
    have branch := Structured.Exec.branch_yes (no := .atom (.copy R.zero R.zero)) condition run
    have frame : ∀ address, (address< g.remainder ∨ g.remainder+g.precision≤address) →
        (extend result (upper data)).2 address=data.2 address := correct.frame
    refine ⟨extend result (upper data),7*g.precision+8,?_,by omega,h.controls.extend result,
      h.sources.remainder_write frame,correct.output_bits,?_⟩
    · convert branch using 1 <;> (try simp only [accept,Geometry.copyLayout]) <;> omega
    · rw [if_pos ordered]
      change value result.2 g.remainder g.precision=next-value source g.denominator g.precision
      have copied := correct.result
      change value result.2 g.remainder g.precision=value data.2 g.difference g.precision at copied
      have equation := h.result
      rw [zero,zero_mul,add_zero] at equation
      omega
  · have notOrdered : ¬value source g.denominator g.precision≤next := fun ordered => zero (test.mpr ordered)
    have condition : ¬(Structured.Condition.eq (low Reg.carry) R.zero).Holds data.word := by
      simpa [Structured.Condition.Holds,NaturalData.word,h.controls.zero] using zero
    have skip := NaturalData.copy_exec data R.zero R.zero (by rw [h.controls.zero]; exact zero_fits width)
    have same : data.set R.zero (data.1 R.zero)=data := by
      apply Prod.ext
      · exact Function.update_eq_self _ _
      · rfl
    rw [same] at skip
    have branch := Structured.Exec.branch_no (yes := accepted) condition skip
    refine ⟨data,3,?_,by omega,h.controls,h.sources,h.remainder_bits,?_⟩
    · exact branch
    · rw [if_neg notOrdered]
      exact h.remainder_value

end LeanTrominoes.Domino.WordRAM.Binary.Remainder
