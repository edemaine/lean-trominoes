/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMNumeratorAbsolute

/-! # Calling binary long remainder inside the numerator test -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Numerator
open ComplexityAbstract.RAM

theorem Geometry.outside (g : Geometry) (i j : Fin 7) (different : i≠j) (a : ℕ) (within : a< g.precision) :
    g.base i+a< g.base j ∨ g.base j+g.precision≤g.base i+a := by
  by_contra h
  push Not at h
  have off : g.base i+a-g.base j< g.precision := by omega
  have diseq := g.disjoint i j different a within (g.base i+a-g.base j) off
  omega

attribute [local simp] Reg.length G.precision G.absolute G.twice G.remainder G.difference
  Remainder.R.numerator Remainder.R.denominator Remainder.R.remainder Remainder.R.difference
  Remainder.R.precision Remainder.R.count Remainder.R.position Remainder.R.zero Remainder.R.one
  middle low NaturalData.set

theorem remainderPrepared_controls (g : Geometry) (data : Data) (h : Controls g data) :
    Remainder.Controls g.remainderGeometry g.precision
      (NaturalData.lower (r:=32) (s:=32) (remainderPrepared data)) := by
  constructor <;> simp [NaturalData.lower,remainderPrepared,Assignments.state,remainderMoves,
    Geometry.remainderGeometry,Geometry.remainderSlot,h.absolute,h.twice,h.remainder,h.difference,h.precision]

structure RemainderResult (g : Geometry) (source : ℕ → ℕ) (result : Data) : Prop where
  controls : Controls g result
  bits : ∀ j< g.precision, result.2 (g.remainder+j)≤1
  frame : ∀ address, (address< g.remainder ∨ g.remainder+g.precision≤address) →
    (address< g.difference ∨ g.difference+g.precision≤address) → result.2 address=source address
  remainder_value : value result.2 g.remainder g.precision=
    value source g.absolute g.precision%value source g.twice g.precision

theorem remainder_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w)
    (controls : Controls g data)
    (bits : ∀ j< g.precision, data.2 (g.absolute+j)≤1)
    (denominatorBits : ∀ j< g.precision, data.2 (g.twice+j)≤1)
    (positive : 0< value data.2 g.twice g.precision)
    (small : 2*value data.2 g.twice g.precision≤2^g.precision)
    (zeros : ∀ j< g.precision, data.2 (g.remainder+j)=0) :
    ∃ result cost, NaturalData.Exec w remainderCode data result cost ∧
      cost≤29*g.precision^2+30*g.precision+15 ∧ RemainderResult g data.2 result := by
  have input : Remainder.Input g.remainderGeometry
      (NaturalData.lower (r:=32) (s:=32) (remainderPrepared data)).2 :=
    ⟨bits,denominatorBits,positive,small⟩
  have widths : Remainder.Widths g.remainderGeometry w := by
    constructor
    · exact width.small
    · exact width.address 4
    · exact width.address 3
    · exact width.address 5
    · exact width.address 6
    · exact width.precision
    · exact width.precision
  obtain ⟨smallResult,cost,run,bound,resultControls,memory,value⟩ := Remainder.program_exec g.remainderGeometry
    (NaturalData.lower (r:=32) (s:=32) (remainderPrepared data)) input widths
    (remainderPrepared_controls g data controls) zeros
  have call := NaturalData.call_exec (r:=32) (s:=32) run
  have full := (remainderSetup_exec g data width controls).seq call
  refine ⟨_,10+cost,full,?_,?_⟩
  · change cost≤(29*g.precision+30)*g.precision+5 at bound
    nlinarith only [bound]
  · exact ⟨controls.after full remainder_preserves,memory.remainder_bits,memory.frame,value⟩

end LeanTrominoes.Domino.WordRAM.Binary.Numerator
