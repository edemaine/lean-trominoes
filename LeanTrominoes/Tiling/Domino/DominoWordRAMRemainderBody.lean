/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainderChoice

/-! # One complete binary long-remainder iteration -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Remainder
open ComplexityAbstract.RAM

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

/-- The complete body scans one actual numerator digit and performs one
long-division reduction, with every load, store, branch and copy charged. -/
theorem body_exec {w : ℕ} (g : Geometry) (source : ℕ → ℕ) (position : ℕ) (data : WideData)
    (input : Input g source) (width : Widths g w) (within : position< g.count)
    (controls : Controls g (position+1) data) (memory : MemoryRepresents g source (position+1) data) :
    ∃ result cost, NaturalData.Exec w body data result cost ∧ cost≤29*g.precision+28 ∧
      Controls g position result ∧ MemoryRepresents g source position result := by
  have bitBound : data.2 (data.1 R.numerator+(data.1 R.position-1))≤1 := by
    rw [controls.numerator,controls.position]
    simp only [Nat.add_sub_cancel]
    rw [memory.numerator position within]
    exact input.numerator_bits position within
  have readRun := readBit_exec data controls.one (by rw [controls.position]; omega)
    (by rw [controls.position]; exact fits_le width.count (by omega))
    (by rw [controls.numerator,controls.position]; exact fits_le width.numerator (by omega))
    (fits_le width.one bitBound)
  have readControls := readState_controls controls
  have readMemory := memory.of_memory (after := readState data) rfl
  have readBitEq := readState_bit within controls memory
  obtain ⟨shiftResult,shiftRun,shiftControls,shiftSources,shiftBits,shiftValue⟩ :=
    shifted_phase g source position (readState data) input width within readControls readMemory readBitEq
  let next := 2*value data.2 g.remainder g.precision+source (g.numerator+position)
  obtain ⟨borrowResult,borrowRun,borrowCorrect⟩ :=
    subtracted_phase g source position next (extend shiftResult (upper (readState data))) input width
      shiftControls shiftSources shiftBits shiftValue
  obtain ⟨result,choiceCost,choiceRun,choiceBound,resultControls,resultSources,resultBits,resultValue⟩ :=
    accept_phase g source position next (extend borrowResult (upper (extend shiftResult (upper (readState data)))))
      width borrowCorrect
  refine ⟨result,3+((7*g.precision+7)+((15*g.precision+10)+choiceCost)),?_,by omega,resultControls,?_⟩
  · exact readRun.seq (shiftRun.seq (borrowRun.seq choiceRun))
  · constructor
    · exact resultSources.numerator
    · exact resultSources.denominator
    · exact resultBits
    · have reduced : remainderStep (value source g.denominator g.precision)
          (value data.2 g.remainder g.precision) (source (g.numerator+position))=
          value source (g.numerator+position) (g.count-position)%value source g.denominator g.precision := by
        rw [memory.result,remainderStep_prefix _ _ _ input.denominator_positive (input.numerator_bits position within)]
        have suffix := value_suffix_step source g.numerator g.count position within
        congr 1
        omega
      calc
        value result.2 g.remainder g.precision=
          remainderStep (value source g.denominator g.precision)
            (value data.2 g.remainder g.precision) (source (g.numerator+position)) := resultValue
        _ = _ := reduced
    · exact resultSources.frame

end LeanTrominoes.Domino.WordRAM.Binary.Remainder
