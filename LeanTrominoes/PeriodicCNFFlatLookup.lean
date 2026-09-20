/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatLayout

/-! # Flat lookup at certified clause and literal addresses -/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open PeriodicCNFFlatEncoding

private theorem get_block {α : Type} (front block suffix : List α) (k : Nat) (hk : k<block.length) :
    (front++block++suffix)[front.length+k]? = block[k]? := by
  rw [List.append_assoc,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

theorem literalEntry_fields (f : PeriodicCNF Nat) {p : Nat} {l : PeriodicLiteral Nat}
    (h : (p,l) ∈ allLiteralEntries 1 f.clauses) (k : Nat) (hk : k<4) :
    (formulaFields f)[p+k]? = (literalFields l)[k]? := by
  obtain ⟨pre,post,he,hp⟩ := allLiteralEntries_split 1 f.clauses h
  have h' := get_block (f.clauses.length::pre) (literalFields l) post k
    (by simpa [literalFields] using hk)
  simpa only [formulaFields,he,List.cons_append,List.length_cons,hp,Nat.add_comm 1] using h'

theorem clauseEntry_fields (f : PeriodicCNF Nat) {p : Nat} {c : PeriodicClause Nat}
    (h : (p,c) ∈ clauseEntries 1 f.clauses) (k : Nat) (hk : k<(clauseFields c).length) :
    (formulaFields f)[p+k]? = (clauseFields c)[k]? := by
  obtain ⟨pre,post,he,hp⟩ := clauseEntries_split 1 f.clauses h
  have h' := get_block (f.clauses.length::pre) (clauseFields c) post k hk
  simpa only [formulaFields,he,List.cons_append,List.length_cons,hp,Nat.add_comm 1] using h'

theorem clauseEntry_header (f : PeriodicCNF Nat) {p : Nat} {c : PeriodicClause Nat}
    (h : (p,c) ∈ clauseEntries 1 f.clauses) :
    (formulaFields f)[p]?.getD 0 = c.length := by
  have e := clauseEntry_fields f h 0 (by simp [clauseFields])
  simpa [clauseFields] using congrArg (fun x => x.getD 0) e

theorem flat_literal_get (ls : List (PeriodicLiteral Nat)) (i : Nat) (hi : i<ls.length)
    (k : Nat) (hk : k<4) :
    (ls.flatMap literalFields)[4*i+k]? = (literalFields ls[i])[k]? := by
  induction ls generalizing i with
  | nil => simp at hi
  | cons l ls ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa [literalFields] using hk)]
    | succ i =>
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [List.getElem?_append_right (by simp [literalFields]; omega)]
      have he : 4*(i+1)+k-(literalFields l).length = 4*i+k := by simp [literalFields]; omega
      rw [he]
      exact ih i (by simpa using hi)

theorem clauseEntry_literal (f : PeriodicCNF Nat) {p : Nat} {c : PeriodicClause Nat}
    (h : (p,c) ∈ clauseEntries 1 f.clauses) (i : Nat) (hi : i<c.length)
    (k : Nat) (hk : k<4) :
    (formulaFields f)[p+1+4*i+k]? = (literalFields c[i])[k]? := by
  have bound : 1+4*i+k < (clauseFields c).length := by
    simp only [clauseFields,List.length_cons,flat_literal_length]
    omega
  rw [show p+1+4*i+k = p+(1+4*i+k) by omega,clauseEntry_fields f h _ bound]
  simp only [clauseFields]
  rw [show 1+4*i+k = (4*i+k)+1 by omega,List.getElem?_cons_succ]
  exact flat_literal_get c i hi k hk

end LeanTrominoes.PeriodicCNF.FlatScanner
