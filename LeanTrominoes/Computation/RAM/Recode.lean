/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComplexityAbstract

/-! # Reinterpreting identical RAM input words

A representation change preserving the physical input words requires no
conversion instructions. The same program and exact execution remain valid.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM

theorem DecidesWithin.recode {A B : Type} {encode : A → List ℤ} {nativeEncode : B → List ℤ}
    {p : A → Prop} {q : B → Prop} {bound bits : A → ℕ} {nativeBound nativeBits : B → ℕ}
    (map : A → B) (words : ∀ a, encode a=nativeEncode (map a))
    (correct : ∀ a, p a ↔ q (map a)) (time : ∀ a, nativeBound (map a)≤bound a)
    (width : ∀ a, nativeBits (map a)≤bits a)
    (native : DecidesWithin nativeEncode q nativeBound nativeBits) :
    DecidesWithin encode p bound bits := by
  obtain ⟨r,program,execution⟩ := native
  refine ⟨r,program,?_⟩
  intro a w enough fits
  obtain ⟨steps,value,run,budget,boolean,answer⟩ := execution (map a) w
    ((width a).trans enough) (by simpa only [words a] using fits)
  refine ⟨steps,value,?_,budget.trans (time a),boolean,?_⟩
  · simpa only [words a] using run
  · exact answer.trans (correct a).symm

/-- Identical physical input words and sizes preserve the polynomial-time
claim without adding a conversion algorithm to its instruction count. -/
theorem PolynomialTime.recode {A B : Type} {encode : A → List ℤ} {nativeEncode : B → List ℤ}
    {size : A → ℕ} {nativeSize : B → ℕ} {p : A → Prop} {q : B → Prop}
    (map : A → B) (words : ∀ a, encode a=nativeEncode (map a))
    (sizes : ∀ a, size a=nativeSize (map a)) (correct : ∀ a, p a ↔ q (map a))
    (native : PolynomialTime nativeEncode nativeSize q) : PolynomialTime encode size p := by
  obtain ⟨constant,degree,coefficient,decision⟩ := native
  refine ⟨constant,degree,coefficient,?_⟩
  exact DecidesWithin.recode map words correct
    (fun a => by simp only [sizes a]; exact le_rfl) (fun a => by simp only [sizes a]; exact le_rfl) decision

end LeanTrominoes.ComplexityAbstract.RAM
