/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalSemantics

/-! # Computing original-origin addresses by ordinary word instructions -/
namespace LeanTrominoes.Domino.WordRAM.OriginPointers128
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128
namespace H
abbrev u : Fin 128 := 64
abbrev v : Fin 128 := 65
abbrev precision : Fin 128 := 72
abbrev first : Fin 128 := 78
abbrev second : Fin 128 := 79
end H
namespace R
abbrev dimension : Fin 128 := 96
abbrev square : Fin 128 := 97
abbrev four : Fin 128 := 98
end R

def header (d : Nat) : Code := .seq (.atom (.constant R.dimension d)) <|
  .seq (.atom (.constant R.square (d*d))) (.atom (.constant R.four 4))
def headed (data : Data) (d : Nat) := ((data.set R.dimension d).set R.square (d*d)).set R.four 4

def pointer (dst src : Fin 128) : Code :=
  .seq (.atom (.arithmetic .mul dst src R.dimension)) <|
  .seq (.atom (.arithmetic .add dst dst R.square)) <|
  .seq (.atom (.arithmetic .mul dst dst H.precision)) (.atom (.arithmetic .add dst dst R.four))

def pointer1 (data : Data) (dst src : Fin 128) := data.set dst (data.1 src*data.1 R.dimension)
def pointer2 (data : Data) (dst src : Fin 128) := (pointer1 data dst src).set dst (data.1 src*data.1 R.dimension+data.1 R.square)
def pointer3 (data : Data) (dst src : Fin 128) := (pointer2 data dst src).set dst ((data.1 src*data.1 R.dimension+data.1 R.square)*data.1 H.precision)
def pointerState (data : Data) (dst src : Fin 128) := (pointer3 data dst src).set dst
  ((data.1 src*data.1 R.dimension+data.1 R.square)*data.1 H.precision+data.1 R.four)

def program (d : Nat) : Code := .seq (header d) <| .seq (pointer H.first H.u) (pointer H.second H.v)

theorem pointer_exec {bound d length : Nat} (data : Data) (dst src : Fin 128)
    (safe : dst≠R.dimension ∧ dst≠R.square ∧ dst≠R.four ∧ dst≠H.precision)
    (dimension : data.1 R.dimension=d) (square : data.1 R.square=d*d)
    (four : data.1 R.four=4) (precision : data.1 H.precision=length) (positive : 0<length)
    (room : (data.1 src*d+d*d)*length+4≤bound) :
    Natural.Exec bound (pointer dst src) data (pointerState data dst src) 4 := by
  have ss := Ne.symm safe.2.1
  have fs := Ne.symm safe.2.2.1
  have ps := Ne.symm safe.2.2.2
  have grow := Nat.mul_le_mul_left (data.1 src*d+d*d) (show 1≤length by omega)
  simp only [Nat.mul_one] at grow
  have a : data.1 src*d≤bound := by omega
  have b : data.1 src*d+d*d≤bound := by omega
  have c : (data.1 src*d+d*d)*length≤bound := by omega
  have first : Natural.Exec bound (.atom (.arithmetic .mul dst src R.dimension)) data (pointer1 data dst src) 1 := by
    exact Natural.Exec.atom (Natural.Step.mul _ _ _ _ (by rw [dimension]; exact a))
  have second : Natural.Exec bound (.atom (.arithmetic .add dst dst R.square)) (pointer1 data dst src) (pointer2 data dst src) 1 := by
    simpa [pointer1,pointer2,NaturalData.set,ss,dimension,square] using
      Natural.Exec.atom (Natural.Step.add (bound:=bound) (pointer1 data dst src) dst dst R.square
        (by simpa [pointer1,NaturalData.set,ss,dimension,square] using b))
  have third : Natural.Exec bound (.atom (.arithmetic .mul dst dst H.precision)) (pointer2 data dst src) (pointer3 data dst src) 1 := by
    simpa [pointer1,pointer2,pointer3,NaturalData.set,ps,dimension,square,precision] using
      Natural.Exec.atom (Natural.Step.mul (bound:=bound) (pointer2 data dst src) dst dst H.precision
        (by simpa [pointer1,pointer2,NaturalData.set,ps,dimension,square,precision] using c))
  have fourth : Natural.Exec bound (.atom (.arithmetic .add dst dst R.four)) (pointer3 data dst src) (pointerState data dst src) 1 := by
    simpa [pointer1,pointer2,pointer3,pointerState,NaturalData.set,fs,dimension,square,precision,four] using
      Natural.Exec.atom (Natural.Step.add (bound:=bound) (pointer3 data dst src) dst dst R.four
        (by simpa [pointer1,pointer2,pointer3,NaturalData.set,fs,dimension,square,precision,four] using room))
  exact first.seq (second.seq (third.seq fourth))

theorem pointerState_value (data : Data) (dst src : Fin 128) :
    (pointerState data dst src).1 dst=(data.1 src*data.1 R.dimension+data.1 R.square)*data.1 H.precision+data.1 R.four := by
  simp [pointerState,NaturalData.set]

theorem pointerState_fixed (data : Data) (dst src reg : Fin 128) (different : reg≠dst) :
    (pointerState data dst src).1 reg=data.1 reg := by
  simp only [pointerState,pointer3,pointer2,pointer1,NaturalData.set,Function.update_of_ne different]

theorem pointerState_memory (data : Data) (dst src : Fin 128) : (pointerState data dst src).2=data.2 := rfl

end LeanTrominoes.Domino.WordRAM.OriginPointers128
