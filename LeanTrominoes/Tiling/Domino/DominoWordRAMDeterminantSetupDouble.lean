/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetupAbsolute

/-! # Copying and doubling the absolute determinant by digit operations -/
namespace LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
open ComplexityAbstract.RAM

noncomputable def Geometry.copyLayout {d : Nat} (g : Geometry d) : ComplementLayout where
  input := g.absolute
  output := g.twice
  length := g.precision
  disjoint := by
    intro i hi j hj _ same
    have apart := g.disjoint 2 1 (by decide)
    rw [g.auxiliary_eq] at apart
    simp only [show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,
      show (1 : Fin 3)≠0 by decide,ite_false,ite_true] at apart
    unfold Apart at apart
    omega

structure DoubleResult {d : Nat} (g : Geometry d) (source : Nat → Nat) (magnitude : Nat) (result : Data) : Prop where
  controls : Controls g result
  bits : ∀ i<g.precision, result.2 (g.twice+i)≤1
  frame : ∀ address, (address<g.twice ∨ g.twice+g.precision≤address) → result.2 address=source address
  value : value result.2 g.twice g.precision=2*magnitude

theorem double_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w)
    (controls : Controls g data) (bits : ∀ i<g.precision, data.2 (g.absolute+i)≤1)
    (magnitude : Nat) (represented : value data.2 g.absolute g.precision=magnitude)
    (room : 2*magnitude<2^g.precision) :
    ∃ result cost, NaturalData.Exec w (.seq copyCode shiftCode) data result cost ∧ cost≤14*g.precision+16 ∧
      DoubleResult g data.2 magnitude result := by
  have args := copyPrepared_controls g data controls
  obtain ⟨copied,copyRun,copyCorrect⟩ := copyProgram_exec g.copyLayout
    (NaturalData.lower (r:=16) (s:=48) (copyPrepared data)) args.1 args.2.1 args.2.2 bits
    width.one width.absolute width.twice width.precision
  let middle : Data := copied.extend (NaturalData.upper (r:=16) (s:=48) (copyPrepared data))
  have copyCall := NaturalData.call_exec (r:=16) (s:=48) copyRun
  have copying := (copySetup_exec g data width controls).seq copyCall
  change NaturalData.Exec w copyCode data middle (4+(7*g.precision+4)) at copying
  have middleControls := controls.after copying copy_preserves
  have middleBits : ∀ i<g.precision, middle.2 (g.twice+i)≤1 := copyCorrect.output_bits
  have middleValue : value middle.2 g.twice g.precision=magnitude := copyCorrect.result.trans represented
  have middleFrame : ∀ address, (address<g.twice ∨ g.twice+g.precision≤address) → middle.2 address=data.2 address := copyCorrect.frame
  have shiftArgs := shiftPrepared_controls g middle middleControls
  obtain ⟨shifted,shiftRun,shiftCorrect⟩ := shiftProgram_exec g.twice g.precision
    (NaturalData.lower (r:=16) (s:=48) (shiftPrepared middle)) shiftArgs.1 shiftArgs.2.1
    (by change (shiftPrepared middle).1 (low Reg.carry)≤1; rw [shiftArgs.2.2]; omega) middleBits width.one width.twice width.precision
  have shiftCall := NaturalData.call_exec (r:=16) (s:=48) shiftRun
  have shifting := (shiftSetup_exec g middle width middleControls).seq shiftCall
  have full := copying.seq shifting
  refine ⟨_,(4+(7*g.precision+4))+(4+(7*g.precision+4)),full,by omega,?_⟩
  constructor
  · exact middleControls.after shifting shift_preserves
  · exact shiftCorrect.output_bits
  · intro address outside
    exact (shiftCorrect.frame address outside).trans (middleFrame address outside)
  · have equation := shiftCorrect.result
    change value shifted.2 g.twice g.precision+shifted.1 Reg.carry*2^g.precision=
      2*value middle.2 g.twice g.precision+0 at equation
    rw [middleValue] at equation
    have carryZero : shifted.1 Reg.carry=0 := by
      by_contra nonzero
      have positive : 1≤shifted.1 Reg.carry := by omega
      have bound := Nat.mul_le_mul_right (2^g.precision) positive
      omega
    rw [carryZero,zero_mul,add_zero] at equation
    exact equation

end LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
