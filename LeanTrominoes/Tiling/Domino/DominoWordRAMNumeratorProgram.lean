/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAssignments
import LeanTrominoes.Tiling.Domino.DominoWordRAMRemainder
import LeanTrominoes.Tiling.Domino.DominoWordRAMSigned
import LeanTrominoes.Tiling.Domino.DominoWordRAMEqualityValue
import LeanTrominoes.Tiling.Domino.DominoWordRAMUnsignedCramer
import LeanTrominoes.Computation.RAM.RegisterFrame

/-! # Testing one signed Cramer numerator by actual binary routines -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Numerator
open ComplexityAbstract.RAM
abbrev Data := NaturalData 64
abbrev Code := Structured.Code 64

namespace G
abbrev precision : Fin 64 := 40
abbrev numerator : Fin 64 := 41
abbrev zero : Fin 64 := 42
abbrev determinant : Fin 64 := 43
abbrev twice : Fin 64 := 44
abbrev absolute : Fin 64 := 45
abbrev remainder : Fin 64 := 46
abbrev difference : Fin 64 := 47
abbrev valid : Fin 64 := 52
abbrev parity : Fin 64 := 53
abbrev isZero : Fin 64 := 54
end G

abbrev low (i : Fin 16) : Fin 64 := i.castAdd 48
abbrev middle (i : Fin 32) : Fin 64 := i.castAdd 32

def absoluteMoves : List (Fin 64 × Fin 64) :=
  [(low Reg.length,G.precision),(low Reg.first,G.numerator),(low Reg.second,G.zero),(low Reg.output,G.absolute)]
def remainderMoves : List (Fin 64 × Fin 64) :=
  [(middle Remainder.R.numerator,G.absolute),(middle Remainder.R.denominator,G.twice),
   (middle Remainder.R.remainder,G.remainder),(middle Remainder.R.difference,G.difference),
   (middle Remainder.R.precision,G.precision),(middle Remainder.R.count,G.precision),
   (middle Remainder.R.position,G.precision)]
def zeroMoves : List (Fin 64 × Fin 64) :=
  [(low Reg.length,G.precision),(low Reg.first,G.remainder),(low Reg.second,G.zero)]
def parityMoves : List (Fin 64 × Fin 64) :=
  [(low Reg.length,G.precision),(low Reg.first,G.remainder),(low Reg.second,G.determinant)]

def absoluteSetup : Code := Assignments.code (low Reg.length) G.precision absoluteMoves
def remainderSetup : Code := .seq (Assignments.code (low Reg.length) G.precision remainderMoves) <|
  .seq (.atom (.constant (middle Remainder.R.zero) 0)) (.atom (.constant (middle Remainder.R.one) 1))
def zeroSetup : Code := Assignments.code (low Reg.length) G.precision zeroMoves
def paritySetup : Code := Assignments.code (low Reg.length) G.precision parityMoves

def absoluteCode : Code := .seq absoluteSetup (Absolute.program.embed 48)
def remainderCode : Code := .seq remainderSetup (Remainder.program.embed 32)
def zeroCode : Code := .seq zeroSetup <| .seq (Equality.program.embed 48) (.atom (.copy G.isZero (low Reg.carry)))
def parityCode : Code := .seq paritySetup <| .seq (Equality.program.embed 48) (.atom (.copy G.parity (low Reg.carry)))
def combine : Code := .atom (.arithmetic .add G.valid G.isZero G.parity)
def program : Code := .seq absoluteCode <| .seq remainderCode <| .seq zeroCode <| .seq parityCode combine

def absolutePrepared (data : Data) : Data := Assignments.state (low Reg.length) G.precision absoluteMoves data
def remainderPrepared (data : Data) : Data :=
  ((Assignments.state (low Reg.length) G.precision remainderMoves data).set (middle Remainder.R.zero) 0).set (middle Remainder.R.one) 1
def zeroPrepared (data : Data) : Data := Assignments.state (low Reg.length) G.precision zeroMoves data
def parityPrepared (data : Data) : Data := Assignments.state (low Reg.length) G.precision parityMoves data

/-- Seven equally precise disjoint blocks. Slot zero is the original signed
numerator, then zero, |det|, 2|det|, absolute numerator, remainder, scratch. -/
structure Geometry where
  base : Fin 7 → ℕ
  precision : ℕ
  disjoint : ∀ i j : Fin 7, i≠j → ∀ a< precision, ∀ b< precision, base i+a≠base j+b

namespace Geometry
abbrev numerator (g : Geometry) := g.base 0
abbrev zero (g : Geometry) := g.base 1
abbrev determinant (g : Geometry) := g.base 2
abbrev twice (g : Geometry) := g.base 3
abbrev absolute (g : Geometry) := g.base 4
abbrev remainder (g : Geometry) := g.base 5
abbrev difference (g : Geometry) := g.base 6

def absoluteLayout (g : Geometry) : Absolute.Layout where
  input := g.numerator
  zero := g.zero
  output := g.absolute
  length := g.precision
  input_safe := fun i hi j hj _ => g.disjoint 4 0 (by decide) i hi j hj
  zero_safe := fun i hi j hj _ => g.disjoint 4 1 (by decide) i hi j hj

def remainderSlot : Fin 4 → Fin 7
  | 0 => 4
  | 1 => 3
  | 2 => 5
  | 3 => 6

theorem remainderSlot_injective : Function.Injective remainderSlot := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp_all [remainderSlot]

def remainderGeometry (g : Geometry) : Remainder.Geometry where
  base := fun i => g.base (remainderSlot i)
  precision := g.precision
  count := g.precision
  disjoint := by
    intro i j different a ha b hb
    apply g.disjoint (remainderSlot i) (remainderSlot j)
      (fun same => different (remainderSlot_injective same)) a (by simpa using ha) b (by simpa using hb)

def zeroLayout (g : Geometry) : Equality.Layout := ⟨g.remainder,g.zero,g.precision⟩
def parityLayout (g : Geometry) : Equality.Layout := ⟨g.remainder,g.determinant,g.precision⟩
end Geometry

structure Controls (g : Geometry) (data : Data) : Prop where
  precision : data.1 G.precision=g.precision
  numerator : data.1 G.numerator=g.numerator
  zero : data.1 G.zero=g.zero
  determinant : data.1 G.determinant=g.determinant
  twice : data.1 G.twice=g.twice
  absolute : data.1 G.absolute=g.absolute
  remainder : data.1 G.remainder=g.remainder
  difference : data.1 G.difference=g.difference

/-- All persistent pointers are private to the arithmetic calls. -/
def PreservesHeaders (code : Code) : Prop :=
  ∀ reg : Fin 64, 40≤ reg.val → reg.val<48 → code.PreservesRegister reg

private def primitiveDecidable {r : ℕ} (i : Fin r) (op : Structured.Primitive r) : Decidable (op.PreservesRegister i) := by
  cases op <;> dsimp only [Structured.Primitive.PreservesRegister] <;> infer_instance

private def codeDecidable {r : ℕ} (i : Fin r) (code : Structured.Code r) : Decidable (code.PreservesRegister i) :=
  match code with
  | .atom op => primitiveDecidable i op
  | .seq a b => by
      letI := codeDecidable i a
      letI := codeDecidable i b
      dsimp only [Structured.Code.PreservesRegister]
      infer_instance
  | .branch _ a b => by
      letI := codeDecidable i a
      letI := codeDecidable i b
      dsimp only [Structured.Code.PreservesRegister]
      infer_instance
  | .loop _ a => codeDecidable i a

local instance {r : ℕ} (i : Fin r) (code : Structured.Code r) : Decidable (code.PreservesRegister i) := codeDecidable i code

theorem absolute_preserves : PreservesHeaders absoluteCode := by unfold PreservesHeaders; decide
theorem remainder_preserves : PreservesHeaders remainderCode := by unfold PreservesHeaders; decide
theorem zero_preserves : PreservesHeaders zeroCode := by unfold PreservesHeaders; decide
theorem parity_preserves : PreservesHeaders parityCode := by unfold PreservesHeaders; decide

theorem parity_preserves_zero : parityCode.PreservesRegister G.isZero := by decide

theorem Controls.after {g : Geometry} {w cost : ℕ} {code : Code} {before after : Data}
    (h : Controls g before) (run : NaturalData.Exec w code before after cost) (preserves : PreservesHeaders code) :
    Controls g after := by
  have same (reg : Fin 64) (high : 40≤ reg.val) (low : reg.val<48) : after.1 reg=before.1 reg := by
    have equal := run.register_eq (preserves reg high low)
    simpa only [NaturalData.word,Int.natCast_inj] using equal
  constructor
  · rw [same _ (by decide) (by decide)]; exact h.precision
  · rw [same _ (by decide) (by decide)]; exact h.numerator
  · rw [same _ (by decide) (by decide)]; exact h.zero
  · rw [same _ (by decide) (by decide)]; exact h.determinant
  · rw [same _ (by decide) (by decide)]; exact h.twice
  · rw [same _ (by decide) (by decide)]; exact h.absolute
  · rw [same _ (by decide) (by decide)]; exact h.remainder
  · rw [same _ (by decide) (by decide)]; exact h.difference

theorem program_size : program.size<512 := by decide

end LeanTrominoes.Domino.WordRAM.Binary.Numerator
