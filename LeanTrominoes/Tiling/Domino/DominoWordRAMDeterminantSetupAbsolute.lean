/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantSetupCircuit

/-! # Actual absolute determinant computation on arbitrary-precision digits -/
namespace LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
open ComplexityAbstract.RAM

structure AbsoluteResult {d : Nat} (g : Geometry d) (source : Nat → Nat) (z : Int) (result : Data) : Prop where
  controls : Controls g result
  bits : ∀ i<g.precision, result.2 (g.absolute+i)≤1
  frame : ∀ address, (address<g.absolute ∨ g.absolute+g.precision≤address) → result.2 address=source address
  magnitude : value result.2 g.absolute g.precision=z.natAbs

theorem absolute_exec {d w : Nat} (g : Geometry d) (data : Data) (width : Widths g w)
    (controls : Controls g data) (positive : 0<g.precision) (z : Int)
    (bits : ∀ i<g.precision, data.2 (g.signed+i)≤1)
    (zeros : ∀ i<g.precision, data.2 (g.zero+i)=0)
    (zFits : Fits g.precision z)
    (encoding : (value data.2 g.signed g.precision : Int)=z%(2^g.precision : Nat)) :
    ∃ result cost, NaturalData.Exec w (absoluteCode d) data result cost ∧ cost≤15*g.precision+22 ∧
      AbsoluteResult g data.2 z result := by
  have pointerRun := pointer_exec g data width controls
  have pointed := pointerState_controls g data controls
  have setup := absoluteSetup_exec g (pointerState d data) width pointed.1 pointed.2
  have args := absolutePrepared_controls g (pointerState d data) pointed.1 pointed.2
  obtain ⟨small,cost,run,budget,correct⟩ := Absolute.program_exec g.absoluteLayout
    (NaturalData.lower (r:=16) (s:=48) (absolutePrepared (pointerState d data))) positive
    args.1 args.2.1 args.2.2.1 args.2.2.2 bits zeros width.small width.signed width.zero width.absolute width.precision
  have call := NaturalData.call_exec (r:=16) (s:=48) run
  have full := pointerRun.seq (setup.seq call)
  refine ⟨_,3+(5+cost),full,by change cost≤15*g.precision+14 at budget; omega,?_⟩
  constructor
  · exact controls.after full (absolute_preserves d)
  · exact correct.output_bits
  · exact correct.frame
  · exact correct.magnitude.trans (twos_complement_magnitude data.2 g.signed g.precision z positive bits zFits encoding)

end LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
