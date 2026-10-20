/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalData
import LeanTrominoes.Computation.RAM.RegisterEmbedding

/-! # Calling natural-valued routines with caller-private registers

This changes only the proof view of registers. The program is embedded into
the original bounded-word machine and retains its exact instruction count.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.NaturalData

def lower {r s : ℕ} (data : NaturalData (r+s)) : NaturalData r :=
  (fun i => data.1 (i.castAdd s),data.2)

def upper {r s : ℕ} (data : NaturalData (r+s)) : Fin s → ℕ :=
  fun i => data.1 (i.natAdd r)

def extend {r s : ℕ} (data : NaturalData r) (tail : Fin s → ℕ) : NaturalData (r+s) :=
  (Fin.addCases (motive := fun _ : Fin (r+s) => ℕ) data.1 tail,data.2)

@[simp] theorem extend_left {r s : ℕ} (data : NaturalData r) (tail : Fin s → ℕ) (i : Fin r) :
    (data.extend tail).1 (i.castAdd s)=data.1 i := by simp [extend]

@[simp] theorem extend_right {r s : ℕ} (data : NaturalData r) (tail : Fin s → ℕ) (i : Fin s) :
    (data.extend tail).1 (i.natAdd r)=tail i := by simp [extend]

@[simp] theorem extend_memory {r s : ℕ} (data : NaturalData r) (tail : Fin s → ℕ) :
    (data.extend tail).2=data.2 := rfl

@[simp] theorem lower_extend {r s : ℕ} (data : NaturalData r) (tail : Fin s → ℕ) :
    lower (data.extend tail)=data := by
  apply Prod.ext
  · funext i
    simp [lower]
  · rfl

@[simp] theorem upper_extend {r s : ℕ} (data : NaturalData r) (tail : Fin s → ℕ) :
    upper (data.extend tail)=tail := by
  funext i
  simp [upper]

@[simp] theorem extend_lower_upper {r s : ℕ} (data : NaturalData (r+s)) :
    (lower data).extend (upper data)=data := by
  apply Prod.ext
  · funext i
    refine Fin.addCases (m:=r) (n:=s) (fun j => ?_) (fun j => ?_) i <;> simp [lower,upper,extend]
  · rfl

theorem extend_word {r s : ℕ} (data : NaturalData r) (tail : Fin s → ℕ) :
    (data.extend tail).word=data.word.extend (fun i => (tail i : ℤ)) := by
  apply Prod.ext
  · funext i
    refine Fin.addCases (m:=r) (n:=s) (fun j => ?_) (fun j => ?_) i <;>
      simp [word,extend,RAM.Data.extend]
  · rfl

/-- Embed a checked subroutine and retain every caller-private register. -/
theorem call_exec {r s w cost : ℕ} {code : Structured.Code r}
    {before : NaturalData (r+s)} {result : NaturalData r}
    (run : Exec w code (lower before) result cost) :
    Exec w (code.embed s) before (result.extend (upper before)) cost := by
  have embedded := run.embed (fun i => (upper before i : ℤ))
  rw [←extend_word,←extend_word,extend_lower_upper] at embedded
  exact embedded

end LeanTrominoes.ComplexityAbstract.RAM.NaturalData
