/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalPrepareGeometry

/-! # Reading the original representative count, precision and input boundary -/
namespace LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
open ComplexityAbstract.RAM
abbrev address : Fin 128 := 0
abbrev inputLength : Fin 128 := 1
abbrev one : Fin 128 := 2

def header : Code :=
  .seq (.atom (.constant address 0)) <|
  .seq (.atom (.load inputLength address)) <|
  .seq (.atom (.constant one 1)) <|
  .seq (.atom (.arithmetic .add H.frontier inputLength one)) <|
  .seq (.atom (.constant address 1)) <|
  .seq (.atom (.load H.n address)) <|
  .seq (.atom (.constant address 3)) (.atom (.load H.precision address))

def h1 (data : Data) := data.set address 0
def h2 (data : Data) := (h1 data).set inputLength (data.2 0)
def h3 (data : Data) := (h2 data).set one 1
def h4 (data : Data) := (h3 data).set H.frontier (data.2 0+1)
def h5 (data : Data) := (h4 data).set address 1
def h6 (data : Data) := (h5 data).set H.n (data.2 1)
def h7 (data : Data) := (h6 data).set address 3
def headerState (data : Data) := (h7 data).set H.precision (data.2 3)

attribute [local simp] address inputLength one H.frontier H.n H.precision
  h1 h2 h3 h4 h5 h6 h7 headerState NaturalData.set

theorem header_exec {n d w : Nat} (B : BasisData n d) (width : Fits w (resourceBound B)) :
    NaturalData.Exec w header (WordRAM.initialData 128 B) (headerState (WordRAM.initialData 128 B)) 8 := by
  let data := WordRAM.initialData 128 B
  have memory0 : data.2 0=(naturalWords B).length := by simp [data,WordRAM.initialData,inputMemory]
  have memory1 : data.2 1=n := by simp [data,WordRAM.initialData,inputMemory,naturalWords]
  have memory3 : data.2 3=WordRAM.precision B := by simp [data,WordRAM.initialData,inputMemory,naturalWords]
  have small := resource_small B
  have lengthBound : (naturalWords B).length≤resourceBound B := by have := resource_input B; unfold inputEnd at this; omega
  have nBound : n≤resourceBound B := by unfold resourceBound; omega
  have first : Natural.Exec (resourceBound B) (.atom (.constant address 0)) data (h1 data) 1 := Natural.Exec.atom (Natural.Step.constant _ _ _ (Nat.zero_le _))
  have second : Natural.Exec (resourceBound B) (.atom (.load inputLength address)) (h1 data) (h2 data) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.load (bound:=resourceBound B) (h1 data) inputLength address (by simp) (by simpa [memory0] using lengthBound))
  have third := Natural.Exec.atom (Natural.Step.constant (h2 data) one 1 (show 1≤resourceBound B by omega))
  have fourth : Natural.Exec (resourceBound B) (.atom (.arithmetic .add H.frontier inputLength one)) (h3 data) (h4 data) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.add (bound:=resourceBound B) (h3 data) H.frontier inputLength one
      (by simpa [memory0,inputEnd] using resource_input B))
  have fifth := Natural.Exec.atom (Natural.Step.constant (h4 data) address 1 (show 1≤resourceBound B by omega))
  have sixth : Natural.Exec (resourceBound B) (.atom (.load H.n address)) (h5 data) (h6 data) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.load (bound:=resourceBound B) (h5 data) H.n address (by simp; omega) (by simpa [memory1] using nBound))
  have seventh := Natural.Exec.atom (Natural.Step.constant (h6 data) address 3 (show 3≤resourceBound B by omega))
  have eighth : Natural.Exec (resourceBound B) (.atom (.load H.precision address)) (h7 data) (headerState data) 1 := by
    simpa using Natural.Exec.atom (Natural.Step.load (bound:=resourceBound B) (h7 data) H.precision address (by simp; omega) (by simpa [memory3] using resource_precision B))
  have trace := first.seq (second.seq (third.seq (fourth.seq (fifth.seq (sixth.seq (seventh.seq eighth))))))
  change Natural.Exec (resourceBound B) header data (headerState data) 8 at trace
  exact trace.compiles width


theorem header_controls {n d : Nat} (B : BasisData n d) :
    (headerState (WordRAM.initialData 128 B)).1 H.n=n ∧
    (headerState (WordRAM.initialData 128 B)).1 H.precision=WordRAM.precision B ∧
    (headerState (WordRAM.initialData 128 B)).1 H.frontier=inputEnd B := by
  simp [WordRAM.initialData,inputMemory,naturalWords,inputEnd]

theorem header_memory (data : Data) : (headerState data).2=data.2 := rfl

end LeanTrominoes.Domino.WordRAM.Binary.GlobalPrepare128
