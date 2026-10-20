/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMNumeratorSetup
import LeanTrominoes.Computation.RAM.NaturalEmbedding

/-! # Calling absolute value inside the Cramer numerator test -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Numerator
open ComplexityAbstract.RAM

attribute [local simp] Reg.length Reg.first Reg.second Reg.output
  G.precision G.numerator G.zero G.absolute low NaturalData.set

theorem absolutePrepared_controls (g : Geometry) (data : Data) (h : Controls g data) :
    (absolutePrepared data).1 (low Reg.length)=g.precision ∧
    (absolutePrepared data).1 (low Reg.first)=g.numerator ∧
    (absolutePrepared data).1 (low Reg.second)=g.zero ∧
    (absolutePrepared data).1 (low Reg.output)=g.absolute := by
  simpa [absolutePrepared,Assignments.state,absoluteMoves] using
    And.intro h.precision (And.intro h.numerator (And.intro h.zero h.absolute))

structure AbsoluteResult (g : Geometry) (source : ℕ → ℕ) (result : Data) : Prop where
  controls : Controls g result
  bits : ∀ j< g.precision, result.2 (g.absolute+j)≤1
  frame : ∀ address, (address< g.absolute ∨ g.absolute+g.precision≤address) → result.2 address=source address
  magnitude : value result.2 g.absolute g.precision=
    if source (g.numerator+(g.precision-1))=1 then 2^g.precision-value source g.numerator g.precision
    else value source g.numerator g.precision

theorem absolute_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w)
    (controls : Controls g data) (positive : 0< g.precision)
    (bits : ∀ j< g.precision, data.2 (g.numerator+j)≤1)
    (zeros : ∀ j< g.precision, data.2 (g.zero+j)=0) :
    ∃ result cost, NaturalData.Exec w absoluteCode data result cost ∧ cost≤15*g.precision+19 ∧
      AbsoluteResult g data.2 result := by
  have args := absolutePrepared_controls g data controls
  obtain ⟨small,cost,run,bound,correct⟩ := Absolute.program_exec g.absoluteLayout
    (NaturalData.lower (r:=16) (s:=48) (absolutePrepared data)) positive
    args.1 args.2.1 args.2.2.1 args.2.2.2 bits zeros width.small
    (width.address 0) (width.address 1) (width.address 4) width.precision
  have call := NaturalData.call_exec (r:=16) (s:=48) run
  have full := (absoluteSetup_exec g data width controls).seq call
  refine ⟨_,5+cost,full,by change cost≤15*g.precision+14 at bound; omega,?_⟩
  exact ⟨controls.after full absolute_preserves,correct.output_bits,correct.frame,correct.magnitude⟩

end LeanTrominoes.Domino.WordRAM.Binary.Numerator
