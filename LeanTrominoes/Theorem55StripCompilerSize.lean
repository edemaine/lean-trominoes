/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripEncoding
import Mathlib.Tactic.Linarith

/-! # Polynomial geometric and output-size bounds for the strip compiler -/

namespace LeanTrominoes.Theorem55StripCompiler

theorem tileCells_length_le (source : PeriodicStrip) :
    (tileCells source).length ≤ (3 * Theorem55StripSource.period source)^2 := by
  unfold tileCells
  rw [List.length_map]
  have h := List.length_filter_le (fun c => !refinedContains source c)
    (Theorem55Compiler.squareList (3 * Theorem55StripSource.period source))
  simpa [Theorem55Compiler.squareList,List.product,List.length_flatMap,List.map_const,List.sum_replicate,pow_two] using h

theorem tileCells_bounds (source : PeriodicStrip) {c : Cell} (hc : c ∈ tileCells source) :
    -4 ≤ c.1 ∧ c.1 < 3 * (Theorem55StripSource.period source : Int) ∧
      0 ≤ c.2 ∧ c.2 < 3 * (Theorem55StripSource.period source : Int) := by
  have member : c ∈ (tileCells source).toFinset := List.mem_toFinset.mpr hc
  rw [tileCells_correct] at member
  simpa using KeyedStripComplement.tile_bounds _ _ member

private theorem encode_int_le {z : Int} {n : Nat} (lo : -4 ≤ z) (hi : z < n) :
    Encodable.encode z ≤ 2*n+8 := by
  cases z with
  | ofNat k =>
    change (k : Int) < n at hi
    rw [Computability.encode_int_ofNat]
    omega
  | negSucc k => rw [Computability.encode_int_negSucc]; omega

private theorem unary_length_bound (values : List Nat) (bound : Nat)
    (bounded : ∀ v ∈ values, v ≤ bound) :
    (Theorem55StripEncoding.unaryFields values).length ≤ values.length * (bound+1) := by
  induction values with
  | nil => simp [Theorem55StripEncoding.unaryFields]
  | cons v rest ih =>
    have hv := bounded v (by simp)
    have hr := ih (fun x hx => bounded x (by simp [hx]))
    simp only [Theorem55StripEncoding.unaryFields,List.flatMap_cons,List.length_append,
      List.length_replicate,List.length_nil,List.length_cons] at *
    nlinarith

/-- A coarse quartic bound in the enlarged side length, for the actual unary encoding.
This is an output-size theorem, not a polynomial-time machine certificate. -/
theorem compile_encoding_length_le (source : PeriodicStrip) :
    (Theorem55StripEncoding.finEncoding.encode (compile source)).length ≤
      (2 + 2 * (3 * Theorem55StripSource.period source)^2) *
        ((3 * Theorem55StripSource.period source)^2 + 2*(3 * Theorem55StripSource.period source)+9) := by
  by_cases valid : source.IsWellFormed
  · let n := 3 * Theorem55StripSource.period source
    let cells := tileCells source
    have length : cells.length ≤ n^2 := tileCells_length_le source
    have bounded : ∀ v ∈ Theorem55StripEncoding.fields (n,cells), v ≤ n^2 + 2*n+8 := by
      intro v hv
      simp only [Theorem55StripEncoding.fields,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,List.mem_flatMap] at hv
      rcases hv with (rfl | rfl) | ⟨c,hc,hv⟩
      · omega
      · omega
      · have bounds := tileCells_bounds source hc
        have hx := encode_int_le bounds.1 (show c.1 < n by simpa [n] using bounds.2.1)
        have hy := encode_int_le (by omega : -4 ≤ c.2) (show c.2 < n by simpa [n] using bounds.2.2.2)
        simp only [PeriodicStripFlatEncoding.cellFields,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl <;> omega
    have fields_length : (Theorem55StripEncoding.fields (n,cells)).length = 2+2*cells.length := by
      have inner : (cells.flatMap PeriodicStripFlatEncoding.cellFields).length = 2*cells.length := by
        induction cells with
        | nil => simp
        | cons c rest ih => simp [List.flatMap_cons,PeriodicStripFlatEncoding.cellFields,ih]; omega
      simp [Theorem55StripEncoding.fields,inner]
      omega
    have bound := unary_length_bound _ _ bounded
    rw [fields_length] at bound
    change (Theorem55StripEncoding.unaryFields (Theorem55StripEncoding.fields (compile source))).length ≤ _
    simp only [compile,valid,ite_true]
    change (Theorem55StripEncoding.unaryFields (Theorem55StripEncoding.fields (n,cells))).length ≤ _
    calc
      _ ≤ (2+2*cells.length)*(n^2+2*n+9) := by simpa [Nat.add_assoc] using bound
      _ ≤ (2+2*n^2)*(n^2+2*n+9) := Nat.mul_le_mul_right _ (by omega)
  · simp only [compile,valid,ite_false]
    change 2 ≤ _
    nlinarith

end LeanTrominoes.Theorem55StripCompiler
