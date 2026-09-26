/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnScalarCompiler

/-! # Keyed column lookup from a relation between queries and table rows -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing
variable {Symbol Row Entry : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Row} {entries : List Symbol → List Entry}
  {query : List Symbol → Row → Nat} {key value : List Symbol → Entry → Nat}
  {result : List Symbol → Row → Nat}

def keyedRelation (queries : Compiler rows query) (keys : Compiler entries key)
    (values : Compiler entries value)
    (consistent : ∀ s a, a ∈ entries s → ∀ b, b ∈ entries s → key s a = key s b → value s a = value s b)
    (present : ∀ s r, r ∈ rows s → ∃ e ∈ entries s, key s e = query s r)
    (correct : ∀ s r, r ∈ rows s → ∀ e, e ∈ entries s → key s e = query s r → value s e = result s r) :
    Compiler rows result := by
  classical
  let datum := fun s code => if h : ∃ e ∈ entries s, key s e = code then value s h.choose else 0
  have table (s : List Symbol) (e : Entry) (he : e ∈ entries s) :
      value s e = datum s (key s e) := by
    have existsEntry : ∃ a ∈ entries s, key s a = key s e := ⟨e,he,rfl⟩
    simp only [datum,dif_pos existsEntry]
    exact consistent s e he _ existsEntry.choose_spec.1 existsEntry.choose_spec.2.symm
  have physical := keyed queries keys values datum table present
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro r hr
  obtain ⟨e,he,hkey⟩ := present s r hr
  change datum s (query s r) = result s r
  rw [← hkey,← table s e he]
  exact correct s r hr e he hkey

end LeanTrominoes.UnaryColumn
end
