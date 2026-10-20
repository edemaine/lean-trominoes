/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDecoderRawExpressions
import LeanTrominoes.Tiling.Domino.DominoWordRAMIntegerExpressions
import LeanTrominoes.Tiling.Domino.DominoWordRAMAssignments
import LeanTrominoes.Tiling.Domino.DominoWordRAMSigned
import LeanTrominoes.Tiling.Domino.DominoWordRAMShift
import LeanTrominoes.Computation.RAM.RegisterFrame

/-! # Fixed determinant preparation using binary arrays

Only the precision and array addresses are word-sized. The signed determinant,
its absolute value and twice its absolute value remain digit arrays.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
open ComplexityAbstract.RAM
abbrev Data := NaturalData 64
abbrev Code := Structured.Code 64
abbrev low (i : Fin 16) : Fin 64 := i.castAdd 48
abbrev circuitReg (i : Fin 17) : Fin 64 := i.castAdd 47
namespace G
abbrev precision : Fin 64 := 56
abbrev circuit : Fin 64 := 57
abbrev zero : Fin 64 := 58
abbrev absolute : Fin 64 := 59
abbrev twice : Fin 64 := 60
abbrev signed : Fin 64 := 61
end G

noncomputable def expression (d : Nat) := Circuit.rawDeterminantCircuit d
abbrev arity (d : Nat) := d*d+2*d
noncomputable def compiled (d : Nat) := (expression d).compile (arity d)
noncomputable def slots (d : Nat) := arity d+(compiled d).nodes.length
noncomputable def outputSlot (d : Nat) := (compiled d).output

/-- Disjoint half-open intervals of equal precision. -/
def Apart (a b length : Nat) : Prop := a+length≤b ∨ b+length≤a

theorem Apart.outside {a b length i : Nat} (h : Apart a b length) (hi : i<length) :
    a+i<b ∨ b+length≤a+i := by unfold Apart at h; omega

theorem Apart.symm {a b length : Nat} (h : Apart a b length) : Apart b a length := Or.symm h

structure Geometry (d : Nat) where
  base : Nat
  precision : Nat
  zero : Nat
  absolute : Nat
  twice : Nat
  auxiliary : Fin 3 → Nat := fun i => if i=0 then zero else if i=1 then absolute else twice
  auxiliary_eq : auxiliary=(fun i => if i=0 then zero else if i=1 then absolute else twice) := by rfl
  disjoint : ∀ i j : Fin 3, i≠j → Apart (auxiliary i) (auxiliary j) precision
  external : ∀ i : Fin 3, base+slots d*precision≤auxiliary i ∨ auxiliary i+precision≤base

namespace Geometry
noncomputable def signed {d : Nat} (g : Geometry d) := Circuit.slotBase g.base g.precision (outputSlot d)
noncomputable def absoluteLayout {d : Nat} (g : Geometry d) : Absolute.Layout where
  input := g.signed
  zero := g.zero
  output := g.absolute
  length := g.precision
  input_safe := by
    intro i hi j hj _ same
    have outputBound := (expression d).output_lt (arity d) (le_refl _)
    have external := g.external 1
    rw [g.auxiliary_eq] at external
    simp only [ite_true,show (1 : Fin 3)≠0 by decide,ite_false] at external
    dsimp [signed,Circuit.slotBase,outputSlot,slots,compiled] at *
    have slotBound := Nat.mul_le_mul_right g.precision (Nat.succ_le_of_lt outputBound)
    rcases external with before | after <;> nlinarith
  zero_safe := by
    intro i hi j hj _ same
    have apart := g.disjoint 1 0 (by decide)
    rw [g.auxiliary_eq] at apart
    simp only [ite_true,show (1 : Fin 3)≠0 by decide,ite_false] at apart
    unfold Apart at apart
    omega
end Geometry

structure Controls {d : Nat} (g : Geometry d) (data : Data) : Prop where
  precision : data.1 G.precision=g.precision
  circuit : data.1 G.circuit=g.base
  zero : data.1 G.zero=g.zero
  absolute : data.1 G.absolute=g.absolute
  twice : data.1 G.twice=g.twice

structure Widths {d : Nat} (g : Geometry d) (w : Nat) : Prop where
  small : Fits w (3 : Nat)
  precision : Fits w g.precision
  circuit : Fits w (Circuit.resourceBound g.base g.precision (slots d))
  zero : Fits w (g.zero+g.precision : Nat)
  absolute : Fits w (g.absolute+g.precision : Nat)
  twice : Fits w (g.twice+g.precision : Nat)

private theorem fits_le {w a b : Nat} (fits : Fits w b) (bound : a≤b) : Fits w a := Allocation.nat_fits_le fits bound

theorem Widths.one {d w : Nat} {g : Geometry d} (h : Widths g w) : Fits w (1 : Nat) := fits_le h.small (by omega)
theorem Widths.zeroValue {d w : Nat} {g : Geometry d} (h : Widths g w) : Fits w (0 : Nat) := fits_le h.small (by omega)
theorem Widths.base {d w : Nat} {g : Geometry d} (h : Widths g w) : Fits w g.base := by
  apply fits_le h.circuit
  unfold Circuit.resourceBound
  omega

noncomputable def circuitMoves : List (Fin 64 × Fin 64) :=
  [(circuitReg Circuit.baseRegister,G.circuit),(low Reg.length,G.precision)]
noncomputable def circuitSetup : Code := Assignments.code (low Reg.length) G.precision circuitMoves
noncomputable def circuitPrepared (data : Data) := Assignments.state (low Reg.length) G.precision circuitMoves data
noncomputable def circuitCode (d : Nat) : Code := .seq circuitSetup ((Circuit.program (compiled d).nodes (arity d)).embed 47)

noncomputable def pointerCode (d : Nat) : Code :=
  .seq (.atom (.constant G.signed (outputSlot d))) <|
  .seq (.atom (.arithmetic .mul G.signed G.signed G.precision))
       (.atom (.arithmetic .add G.signed G.circuit G.signed))
noncomputable def pointerState (d : Nat) (data : Data) :=
  ((data.set G.signed (outputSlot d)).set G.signed (outputSlot d*data.1 G.precision)).set G.signed
    (data.1 G.circuit+outputSlot d*data.1 G.precision)

def absoluteMoves : List (Fin 64 × Fin 64) :=
  [(low Reg.length,G.precision),(low Reg.first,G.signed),(low Reg.second,G.zero),(low Reg.output,G.absolute)]
def absoluteSetup : Code := Assignments.code (low Reg.length) G.precision absoluteMoves
def absolutePrepared (data : Data) := Assignments.state (low Reg.length) G.precision absoluteMoves data
noncomputable def absoluteCode (d : Nat) : Code := .seq (pointerCode d) <| .seq absoluteSetup (Absolute.program.embed 48)

def copyMoves : List (Fin 64 × Fin 64) :=
  [(low Reg.length,G.precision),(low Reg.first,G.absolute),(low Reg.output,G.twice)]
def copySetup : Code := Assignments.code (low Reg.length) G.precision copyMoves
def copyPrepared (data : Data) := Assignments.state (low Reg.length) G.precision copyMoves data
def copyCode : Code := .seq copySetup (copyProgram.embed 48)

def shiftMoves : List (Fin 64 × Fin 64) := [(low Reg.length,G.precision),(low Reg.first,G.twice)]
def shiftSetup : Code := .seq (Assignments.code (low Reg.length) G.precision shiftMoves) (.atom (.constant (low Reg.carry) 0))
def shiftPrepared (data : Data) := (Assignments.state (low Reg.length) G.precision shiftMoves data).set (low Reg.carry) 0
def shiftCode : Code := .seq shiftSetup (shiftProgram.embed 48)
noncomputable def program (d : Nat) : Code := .seq (circuitCode d) <| .seq (absoluteCode d) <| .seq copyCode shiftCode

end LeanTrominoes.Domino.WordRAM.Binary.DeterminantSetup
