/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMNumeratorProgram

/-! # Checked argument setup in the Cramer numerator tester -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Numerator
open ComplexityAbstract.RAM

structure Widths (g : Geometry) (w : ℕ) : Prop where
  small : Fits w (3:ℕ)
  precision : Fits w g.precision
  address : ∀ slot, Fits w (g.base slot+g.precision : ℕ)

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem Widths.pointer {g : Geometry} {w : ℕ} (h : Widths g w) (slot : Fin 7) : Fits w (g.base slot) :=
  fits_le (h.address slot) (Nat.le_add_right _ _)
theorem Widths.one {g : Geometry} {w : ℕ} (h : Widths g w) : Fits w (1:ℕ) := fits_le h.small (by omega)
theorem Widths.zero {g : Geometry} {w : ℕ} (h : Widths g w) : Fits w (0:ℕ) := fits_le h.small (by omega)

attribute [local simp] Reg.length Reg.first Reg.second Reg.output Reg.carry
  G.precision G.numerator G.zero G.determinant G.twice G.absolute G.remainder G.difference G.valid G.parity G.isZero
  Remainder.R.numerator Remainder.R.denominator Remainder.R.remainder Remainder.R.difference
  Remainder.R.precision Remainder.R.count Remainder.R.position Remainder.R.zero Remainder.R.one
  low middle NaturalData.set

theorem absoluteSetup_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w) (controls : Controls g data) :
    NaturalData.Exec w absoluteSetup data (absolutePrepared data) 5 := by
  apply Assignments.exec data (low Reg.length) G.precision absoluteMoves (by rw [controls.precision]; exact width.precision)
  · intro p hp
    simp only [absoluteMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact controls.precision ▸ width.precision
    · exact controls.numerator ▸ width.pointer 0
    · exact controls.zero ▸ width.pointer 1
    · exact controls.absolute ▸ width.pointer 4
  · simp [absoluteMoves]
  · simp [absoluteMoves]

theorem remainderSetup_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w) (controls : Controls g data) :
    NaturalData.Exec w remainderSetup data (remainderPrepared data) 10 := by
  have copies : NaturalData.Exec w (Assignments.code (low Reg.length) G.precision remainderMoves) data
      (Assignments.state (low Reg.length) G.precision remainderMoves data) 8 := by
    apply Assignments.exec data (low Reg.length) G.precision remainderMoves (by rw [controls.precision]; exact width.precision)
    · intro p hp
      simp only [remainderMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact controls.absolute ▸ width.pointer 4
      · exact controls.twice ▸ width.pointer 3
      · exact controls.remainder ▸ width.pointer 5
      · exact controls.difference ▸ width.pointer 6
      all_goals exact controls.precision ▸ width.precision
    · simp [remainderMoves]
    · simp [remainderMoves]
  have zero := NaturalData.constant_exec (Assignments.state (low Reg.length) G.precision remainderMoves data) (middle Remainder.R.zero) 0 width.zero
  have one := NaturalData.constant_exec ((Assignments.state (low Reg.length) G.precision remainderMoves data).set (middle Remainder.R.zero) 0)
    (middle Remainder.R.one) 1 width.one
  exact copies.seq (zero.seq one)

theorem zeroSetup_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w) (controls : Controls g data) :
    NaturalData.Exec w zeroSetup data (zeroPrepared data) 4 := by
  apply Assignments.exec data (low Reg.length) G.precision zeroMoves (by rw [controls.precision]; exact width.precision)
  · intro p hp
    simp only [zeroMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact controls.precision ▸ width.precision
    · exact controls.remainder ▸ width.pointer 5
    · exact controls.zero ▸ width.pointer 1
  · simp [zeroMoves]
  · simp [zeroMoves]

theorem paritySetup_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w) (controls : Controls g data) :
    NaturalData.Exec w paritySetup data (parityPrepared data) 4 := by
  apply Assignments.exec data (low Reg.length) G.precision parityMoves (by rw [controls.precision]; exact width.precision)
  · intro p hp
    simp only [parityMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact controls.precision ▸ width.precision
    · exact controls.remainder ▸ width.pointer 5
    · exact controls.determinant ▸ width.pointer 2
  · simp [parityMoves]
  · simp [parityMoves]

end LeanTrominoes.Domino.WordRAM.Binary.Numerator
