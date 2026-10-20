/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetupArguments

/-! # Runtime pointers and binary argument assignments for determinant setup -/
namespace LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
open ComplexityAbstract.RAM
attribute [local simp] Reg.length Reg.first Reg.second Reg.output Reg.carry low
  G.precision G.circuit G.zero G.absolute G.twice G.signed NaturalData.set

theorem Widths.signed {d w : Nat} {g : Geometry d} (h : Widths g w) : Fits w (g.signed+g.precision : Nat) := by
  exact Circuit.resource_end_fits h.circuit ((expression d).output_lt (arity d) (le_refl _)).le

theorem pointer_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w) (h : Controls g data) :
    NaturalData.Exec w (pointerCode d) data (pointerState d data) 3 := by
  have within : outputSlot d≤slots d := ((expression d).output_lt (arity d) (le_refl _)).le
  have constantFits : Fits w (outputSlot d) := by
    apply Allocation.nat_fits_le width.circuit
    unfold Circuit.resourceBound
    nlinarith
  have productFits : Fits w (outputSlot d*g.precision : Nat) := by
    apply Allocation.nat_fits_le width.circuit
    have := Nat.mul_le_mul_right g.precision within
    unfold Circuit.resourceBound
    nlinarith
  let a := data.set G.signed (outputSlot d)
  let b := a.set G.signed (outputSlot d*data.1 G.precision)
  have first := NaturalData.constant_exec data G.signed (outputSlot d) constantFits
  have second : NaturalData.Exec w (.atom (.arithmetic .mul G.signed G.signed G.precision)) a b 1 := by
    simpa [b,a,h.precision] using NaturalData.mul_exec a G.signed G.signed G.precision
      (by simpa [a,h.precision] using productFits)
  have third : NaturalData.Exec w (.atom (.arithmetic .add G.signed G.circuit G.signed)) b (pointerState d data) 1 := by
    have address : Fits w (b.1 G.circuit+b.1 G.signed : Nat) := by
      apply Allocation.nat_fits_le width.signed
      simp [b,a,h.precision,h.circuit,Geometry.signed,Circuit.slotBase]
    simpa [pointerState,b,a] using NaturalData.add_exec b G.signed G.circuit G.signed address
  exact first.seq (second.seq third)

theorem pointerState_controls {d : Nat} (g : Geometry d) (data : Data) (h : Controls g data) :
    Controls g (pointerState d data) ∧ (pointerState d data).1 G.signed=g.signed := by
  constructor
  · constructor <;> simp [pointerState,h.precision,h.circuit,h.zero,h.absolute,h.twice]
  · simp [pointerState,h.precision,h.circuit,Geometry.signed,Circuit.slotBase]

theorem absoluteSetup_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w)
    (h : Controls g data) (signed : data.1 G.signed=g.signed) :
    NaturalData.Exec w absoluteSetup data (absolutePrepared data) 5 := by
  apply Assignments.exec data (low Reg.length) G.precision absoluteMoves (h.precision ▸ width.precision)
  · intro p hp
    simp only [absoluteMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h.precision ▸ width.precision
    · rw [signed]; exact Allocation.nat_fits_le width.signed (Nat.le_add_right _ _)
    · rw [h.zero]; exact Allocation.nat_fits_le width.zero (Nat.le_add_right _ _)
    · rw [h.absolute]; exact Allocation.nat_fits_le width.absolute (Nat.le_add_right _ _)
  · simp [absoluteMoves]
  · simp [absoluteMoves]

theorem absolutePrepared_controls {d : Nat} (g : Geometry d) (data : Data)
    (h : Controls g data) (signed : data.1 G.signed=g.signed) :
    (absolutePrepared data).1 (low Reg.length)=g.precision ∧
    (absolutePrepared data).1 (low Reg.first)=g.signed ∧
    (absolutePrepared data).1 (low Reg.second)=g.zero ∧
    (absolutePrepared data).1 (low Reg.output)=g.absolute := by
  simp [absolutePrepared,Assignments.state,absoluteMoves,h.precision,signed,h.zero,h.absolute]

theorem copySetup_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w) (h : Controls g data) :
    NaturalData.Exec w copySetup data (copyPrepared data) 4 := by
  apply Assignments.exec data (low Reg.length) G.precision copyMoves (h.precision ▸ width.precision)
  · intro p hp
    simp only [copyMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact h.precision ▸ width.precision
    · rw [h.absolute]; exact Allocation.nat_fits_le width.absolute (Nat.le_add_right _ _)
    · rw [h.twice]; exact Allocation.nat_fits_le width.twice (Nat.le_add_right _ _)
  · simp [copyMoves]
  · simp [copyMoves]

theorem copyPrepared_controls {d : Nat} (g : Geometry d) (data : Data) (h : Controls g data) :
    (copyPrepared data).1 (low Reg.length)=g.precision ∧
    (copyPrepared data).1 (low Reg.first)=g.absolute ∧
    (copyPrepared data).1 (low Reg.output)=g.twice := by
  simp [copyPrepared,Assignments.state,copyMoves,h.precision,h.absolute,h.twice]

theorem shiftSetup_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w) (h : Controls g data) :
    NaturalData.Exec w shiftSetup data (shiftPrepared data) 4 := by
  have copies : NaturalData.Exec w (Assignments.code (low Reg.length) G.precision shiftMoves) data
      (Assignments.state (low Reg.length) G.precision shiftMoves data) 3 := by
    apply Assignments.exec data (low Reg.length) G.precision shiftMoves (h.precision ▸ width.precision)
    · intro p hp
      simp only [shiftMoves,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl
      · exact h.precision ▸ width.precision
      · rw [h.twice]; exact Allocation.nat_fits_le width.twice (Nat.le_add_right _ _)
    · simp [shiftMoves]
    · simp [shiftMoves]
  exact copies.seq (NaturalData.constant_exec _ (low Reg.carry) 0 width.zeroValue)

theorem shiftPrepared_controls {d : Nat} (g : Geometry d) (data : Data) (h : Controls g data) :
    (shiftPrepared data).1 (low Reg.length)=g.precision ∧
    (shiftPrepared data).1 (low Reg.first)=g.twice ∧ (shiftPrepared data).1 (low Reg.carry)=0 := by
  simp [shiftPrepared,Assignments.state,shiftMoves,h.precision,h.twice]

end LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
