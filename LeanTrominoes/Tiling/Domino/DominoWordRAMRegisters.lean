/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAddition
import LeanTrominoes.Computation.RAM.RegisterEmbedding

/-! # Register-private calls to binary arithmetic routines -/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

abbrev WideData := NaturalData 32
abbrev WideCode := Structured.Code 32

def lower (data : WideData) : Data := (fun i => data.1 (i.castAdd 16),data.2)
def upper (data : WideData) : Fin 16 → ℕ := fun i => data.1 (i.natAdd 16)
def extend (data : Data) (tail : Fin 16 → ℕ) : WideData := (Fin.addCases (motive := fun _ : Fin (16+16) => ℕ) data.1 tail,data.2)

@[simp] theorem extend_left (data : Data) (tail : Fin 16 → ℕ) (i : Fin 16) :
    (extend data tail).1 (i.castAdd 16)=data.1 i := by simp only [extend,Fin.addCases_left,Fin.addCases_right]

@[simp] theorem extend_right (data : Data) (tail : Fin 16 → ℕ) (i : Fin 16) :
    (extend data tail).1 (i.natAdd 16)=tail i := by simp only [extend,Fin.addCases_left,Fin.addCases_right]

@[simp] theorem extend_memory (data : Data) (tail : Fin 16 → ℕ) : (extend data tail).2=data.2 := rfl

@[simp] theorem lower_extend (data : Data) (tail : Fin 16 → ℕ) : lower (extend data tail)=data := by
  apply Prod.ext
  · funext i
    simp [lower]
  · rfl

@[simp] theorem upper_extend (data : Data) (tail : Fin 16 → ℕ) : upper (extend data tail)=tail := by
  funext i
  simp only [upper,extend,Fin.addCases_left,Fin.addCases_right]

@[simp] theorem extend_lower_upper (data : WideData) : extend (lower data) (upper data)=data := by
  apply Prod.ext
  · funext i
    refine Fin.addCases (n:=16) (m:=16) (fun j => ?_) (fun j => ?_) i <;> simp only [lower,upper,extend,Fin.addCases_left,Fin.addCases_right]
  · rfl

theorem extend_word (data : Data) (tail : Fin 16 → ℕ) :
    (extend data tail).word=data.word.extend (fun i => (tail i : ℤ)) := by
  apply Prod.ext
  · funext i
    refine Fin.addCases (n:=16) (m:=16) (fun j => ?_) (fun j => ?_) i <;>
      simp only [NaturalData.word,extend,ComplexityAbstract.RAM.Data.extend,Fin.addCases_left,Fin.addCases_right]
  · rfl

/-- A checked execution can be called in a larger register file. All sixteen
caller-private registers retain their exact values. -/
theorem call_exec {w cost : ℕ} {code : Code} {before : WideData} {result : Data}
    (run : NaturalData.Exec w code (lower before) result cost) :
    NaturalData.Exec w (code.embed 16) before (extend result (upper before)) cost := by
  have embedded := run.embed (fun i => (upper before i : ℤ))
  rw [← extend_word,← extend_word,extend_lower_upper] at embedded
  exact embedded

@[simp] theorem lower_memory (data : WideData) : (lower data).2=data.2 := rfl
@[simp] theorem lower_register (data : WideData) (i : Fin 16) : (lower data).1 i=data.1 (i.castAdd 16) := rfl

@[simp] theorem upper_set_lower (data : WideData) (i : Fin 16) (value : ℕ) :
    upper (data.set (i.castAdd 16) value)=upper data := by
  funext j
  have different : j.natAdd 16≠i.castAdd 16 := by
    intro same
    have eq := congrArg Fin.val same
    simp only [Fin.val_natAdd,Fin.val_castAdd] at eq
    have := i.isLt
    omega
  simp only [upper,NaturalData.set,Function.update_of_ne different]

/-- Exact equality of the caller's sixteen private registers. -/
def TailEq (before after : WideData) : Prop := upper after=upper before

theorem extend_tail (before : WideData) (result : Data) : TailEq before (extend result (upper before)) := by
  simp [TailEq]

end LeanTrominoes.Domino.WordRAM.Binary
