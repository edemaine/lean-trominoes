/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.NaturalData

/-! # Checked natural multiplication, division, and remainder instructions

These lemmas execute the original signed-word arithmetic instructions. Every
written result must fit; there is no arithmetic instruction on larger values.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.NaturalData

theorem mul_exec {r w : ℕ} (data : NaturalData r) (dst left right : Fin r)
    (fits : Fits w (data.1 left*data.1 right : ℕ)) :
    Exec w (.atom (.arithmetic .mul dst left right)) data (data.set dst (data.1 left*data.1 right)) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  simp only [Nat.cast_mul] at fits
  simp [Structured.Primitive.eval,Arithmetic.eval,word,fits]

theorem div_exec {r w : ℕ} (data : NaturalData r) (dst left right : Fin r)
    (fits : Fits w (data.1 left/data.1 right : ℕ)) :
    Exec w (.atom (.arithmetic .div dst left right)) data (data.set dst (data.1 left/data.1 right)) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  simp only [Int.natCast_ediv] at fits
  simp [Structured.Primitive.eval,Arithmetic.eval,word,fits,Int.natCast_ediv]

theorem mod_exec {r w : ℕ} (data : NaturalData r) (dst left right : Fin r)
    (fits : Fits w (data.1 left%data.1 right : ℕ)) :
    Exec w (.atom (.arithmetic .mod dst left right)) data (data.set dst (data.1 left%data.1 right)) 1 := by
  rw [Exec,word_set]
  apply Structured.Exec.atom
  simp only [Int.natCast_emod] at fits
  simp [Structured.Primitive.eval,Arithmetic.eval,word,fits,Int.natCast_emod]

end LeanTrominoes.ComplexityAbstract.RAM.NaturalData
