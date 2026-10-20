/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMNumeratorRemainder

/-! # Equality phases of the actual Cramer numerator test -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Numerator
open ComplexityAbstract.RAM

attribute [local simp] Reg.length Reg.first Reg.second Reg.carry G.precision G.remainder
  G.zero G.determinant G.isZero G.parity low NaturalData.set

structure EqualityResult (g : Geometry) (source : ℕ → ℕ) (target : ℕ) (flag : Fin 64) (result : Data) : Prop where
  controls : Controls g result
  memory : result.2=source
  bounded : result.1 flag≤1
  equal : result.1 flag=1 ↔ value source g.remainder g.precision=value source target g.precision

theorem zero_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w)
    (controls : Controls g data) (bits : ∀ j< g.precision, data.2 (g.remainder+j)≤1)
    (otherBits : ∀ j< g.precision, data.2 (g.base 1+j)≤1) :
    ∃ result cost, NaturalData.Exec w zeroCode data result cost ∧ cost≤10*g.precision+10 ∧
      EqualityResult g data.2 (g.base 1) G.isZero result := by
  have args : (zeroPrepared data).1 (low Reg.length)=g.precision ∧
      (zeroPrepared data).1 (low Reg.first)=g.remainder ∧
      (zeroPrepared data).1 (low Reg.second)=g.base 1 := by
    simp [zeroPrepared,Assignments.state,zeroMoves,controls.precision,controls.remainder,
      controls.zero,controls.determinant]
  obtain ⟨smallResult,cost,run,bound,correct,equal⟩ := Equality.program_value_exec g.zeroLayout
    (NaturalData.lower (r:=16) (s:=48) (zeroPrepared data))
    args.1 args.2.1 args.2.2 bits otherBits width.one (width.address 5) (width.address 1) width.precision
  have call := NaturalData.call_exec (r:=16) (s:=48) run
  have flagFits : Fits w ((smallResult.extend (NaturalData.upper (r:=16) (s:=48) (zeroPrepared data))).1 (low Reg.carry)) := by
    simpa only [NaturalData.extend_left] using (by
      refine ⟨width.one.1,?_,lt_of_le_of_lt (by exact_mod_cast correct.carry) width.one.2.2⟩
      exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _))
  have save := NaturalData.copy_exec (smallResult.extend (NaturalData.upper (r:=16) (s:=48) (zeroPrepared data))) G.isZero (low Reg.carry) flagFits
  have full := (zeroSetup_exec g data width controls).seq (call.seq save)
  refine ⟨_,4+(cost+1),full,?_,?_⟩
  · change cost≤10*g.precision+5 at bound
    omega
  · constructor
    · exact controls.after full zero_preserves
    · exact correct.memory
    · change smallResult.1 Reg.carry≤1
      exact correct.carry
    · change (smallResult.1 Reg.carry=1 ↔ value data.2 g.remainder g.precision=value data.2 _ g.precision) at equal
      change (smallResult.1 Reg.carry=1 ↔ _)
      exact equal

theorem parity_exec {w : ℕ} (g : Geometry) (data : Data) (width : Widths g w)
    (controls : Controls g data) (bits : ∀ j< g.precision, data.2 (g.remainder+j)≤1)
    (otherBits : ∀ j< g.precision, data.2 (g.base 2+j)≤1) :
    ∃ result cost, NaturalData.Exec w parityCode data result cost ∧ cost≤10*g.precision+10 ∧
      EqualityResult g data.2 (g.base 2) G.parity result := by
  have args : (parityPrepared data).1 (low Reg.length)=g.precision ∧
      (parityPrepared data).1 (low Reg.first)=g.remainder ∧
      (parityPrepared data).1 (low Reg.second)=g.base 2 := by
    simp [parityPrepared,Assignments.state,parityMoves,controls.precision,controls.remainder,
      controls.zero,controls.determinant]
  obtain ⟨smallResult,cost,run,bound,correct,equal⟩ := Equality.program_value_exec g.parityLayout
    (NaturalData.lower (r:=16) (s:=48) (parityPrepared data))
    args.1 args.2.1 args.2.2 bits otherBits width.one (width.address 5) (width.address 2) width.precision
  have call := NaturalData.call_exec (r:=16) (s:=48) run
  have flagFits : Fits w ((smallResult.extend (NaturalData.upper (r:=16) (s:=48) (parityPrepared data))).1 (low Reg.carry)) := by
    simpa only [NaturalData.extend_left] using (by
      refine ⟨width.one.1,?_,lt_of_le_of_lt (by exact_mod_cast correct.carry) width.one.2.2⟩
      exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _))
  have save := NaturalData.copy_exec (smallResult.extend (NaturalData.upper (r:=16) (s:=48) (parityPrepared data))) G.parity (low Reg.carry) flagFits
  have full := (paritySetup_exec g data width controls).seq (call.seq save)
  refine ⟨_,4+(cost+1),full,?_,?_⟩
  · change cost≤10*g.precision+5 at bound
    omega
  · constructor
    · exact controls.after full parity_preserves
    · exact correct.memory
    · change smallResult.1 Reg.carry≤1
      exact correct.carry
    · change (smallResult.1 Reg.carry=1 ↔ value data.2 g.remainder g.precision=value data.2 _ g.precision) at equal
      change (smallResult.1 Reg.carry=1 ↔ _)
      exact equal

end LeanTrominoes.Domino.WordRAM.Binary.Numerator
