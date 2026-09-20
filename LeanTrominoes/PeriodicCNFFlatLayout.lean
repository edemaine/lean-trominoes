/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFlatFieldCountSpace
import Mathlib.Data.Nat.BitIndices

/-! # Addresses and bit-mask semantics of flat CNF fields -/
namespace LeanTrominoes.PeriodicCNF.FlatScanner
open PeriodicCNFFlatEncoding

def literalEntries (start : Nat) : List (PeriodicLiteral Nat) → List (Nat × PeriodicLiteral Nat)
  | [] => []
  | l :: ls => (start,l) :: literalEntries (start+4) ls

def clauseEntries (start : Nat) : List (PeriodicClause Nat) → List (Nat × PeriodicClause Nat)
  | [] => []
  | c :: cs => (start,c) :: clauseEntries (start+1+4*c.length) cs

def allLiteralEntries (start : Nat) : List (PeriodicClause Nat) → List (Nat × PeriodicLiteral Nat)
  | [] => []
  | c :: cs => literalEntries (start+1) c ++ allLiteralEntries (start+1+4*c.length) cs

theorem flat_literal_length (ls : List (PeriodicLiteral Nat)) :
    (ls.flatMap literalFields).length = 4*ls.length := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp [literalFields,ih]; omega

theorem literalEntries_bounds (start : Nat) (ls : List (PeriodicLiteral Nat))
    {entry : Nat × PeriodicLiteral Nat} (h : entry ∈ literalEntries start ls) :
    start ≤ entry.1 ∧ entry.1 < start+4*ls.length := by
  induction ls generalizing start with
  | nil => simp [literalEntries] at h
  | cons l ls ih =>
    simp only [literalEntries,List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have b := ih (start+4) h
      simp only [List.length_cons]
      omega

theorem clauseEntries_bounds (start : Nat) (cs : List (PeriodicClause Nat))
    {entry : Nat × PeriodicClause Nat} (h : entry ∈ clauseEntries start cs) :
    start ≤ entry.1 ∧ entry.1 < start+(cs.flatMap clauseFields).length := by
  induction cs generalizing start with
  | nil => simp [clauseEntries] at h
  | cons c cs ih =>
    simp only [clauseEntries,List.mem_cons] at h
    simp only [List.flatMap_cons,clauseFields,List.length_append,List.length_cons,flat_literal_length]
    rcases h with rfl | h
    · simp
    · have b := ih (start+1+4*c.length) h
      omega

theorem allLiteralEntries_bounds (start : Nat) (cs : List (PeriodicClause Nat))
    {entry : Nat × PeriodicLiteral Nat} (h : entry ∈ allLiteralEntries start cs) :
    start ≤ entry.1 ∧ entry.1 < start+(cs.flatMap clauseFields).length := by
  induction cs generalizing start with
  | nil => simp [allLiteralEntries] at h
  | cons c cs ih =>
    simp only [allLiteralEntries,List.mem_append] at h
    simp only [List.flatMap_cons,clauseFields,List.length_append,List.length_cons,flat_literal_length]
    rcases h with h | h
    · have b := literalEntries_bounds (start+1) c h
      omega
    · have b := ih (start+1+4*c.length) h
      omega

theorem literalEntries_sorted (start : Nat) (ls : List (PeriodicLiteral Nat)) :
    ((literalEntries start ls).map Prod.fst).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  induction ls generalizing start with
  | nil => simp [literalEntries]
  | cons l ls ih =>
    simp only [literalEntries,List.map_cons,List.pairwise_cons]
    refine ⟨?_,ih _⟩
    intro p hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    have b := literalEntries_bounds (start+4) ls he
    omega

theorem clauseEntries_sorted (start : Nat) (cs : List (PeriodicClause Nat)) :
    ((clauseEntries start cs).map Prod.fst).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  induction cs generalizing start with
  | nil => simp [clauseEntries]
  | cons c cs ih =>
    simp only [clauseEntries,List.map_cons,List.pairwise_cons]
    refine ⟨?_,ih _⟩
    intro p hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    have b := clauseEntries_bounds (start+1+4*c.length) cs he
    omega

theorem allLiteralEntries_sorted (start : Nat) (cs : List (PeriodicClause Nat)) :
    ((allLiteralEntries start cs).map Prod.fst).SortedLT := by
  rw [List.sortedLT_iff_pairwise]
  induction cs generalizing start with
  | nil => simp [allLiteralEntries]
  | cons c cs ih =>
    simp only [allLiteralEntries,List.map_append,List.pairwise_append]
    refine ⟨(literalEntries_sorted _ _).pairwise,ih _,?_⟩
    intro p hp q hq
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    obtain ⟨e',he',rfl⟩ := List.mem_map.mp hq
    have b := literalEntries_bounds (start+1) c he
    have b' := allLiteralEntries_bounds (start+1+4*c.length) cs he'
    omega

theorem literalRunMarks_eq_sum (start : Nat) (ls : List (PeriodicLiteral Nat)) :
    literalRunMarks start ls.length = ((literalEntries start ls).map fun e => 2^e.1).sum := by
  induction ls generalizing start with
  | nil => rfl
  | cons l ls ih => simp [literalRunMarks,literalEntries,ih]

theorem clauseMarks_eq_sum (start : Nat) (cs : List (PeriodicClause Nat)) :
    clauseMarks start cs = ((clauseEntries start cs).map fun e => 2^e.1).sum := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih => simp [clauseMarks,clauseEntries,ih]

theorem literalMarks_eq_sum (start : Nat) (cs : List (PeriodicClause Nat)) :
    literalMarks start cs = ((allLiteralEntries start cs).map fun e => 2^e.1).sum := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih => simp [literalMarks,allLiteralEntries,literalRunMarks_eq_sum,ih]

private theorem bit_sum_iff {α : Type} (entries : List (Nat × α)) (p : Nat)
    (sorted : (entries.map Prod.fst).SortedLT) :
    ((entries.map fun (e : Nat × α) => 2^e.1).sum).testBit p = true ↔ ∃ x, (p,x) ∈ entries := by
  rw [← Nat.mem_bitIndices]
  have h := Nat.bitIndices_sum_map_two_pow sorted
  simp only [List.map_map,Function.comp_def] at h
  rw [h]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨q,x⟩,hx,hq⟩
    exact ⟨x,by simpa using hq ▸ hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨(p,x),hx,rfl⟩

theorem clauseMarks_testBit (start : Nat) (cs : List (PeriodicClause Nat)) (p : Nat) :
    (clauseMarks start cs).testBit p = true ↔ ∃ c, (p,c) ∈ clauseEntries start cs := by
  rw [clauseMarks_eq_sum]
  exact bit_sum_iff _ _ (clauseEntries_sorted _ _)

theorem literalMarks_testBit (start : Nat) (cs : List (PeriodicClause Nat)) (p : Nat) :
    (literalMarks start cs).testBit p = true ↔ ∃ l, (p,l) ∈ allLiteralEntries start cs := by
  rw [literalMarks_eq_sum]
  exact bit_sum_iff _ _ (allLiteralEntries_sorted _ _)

theorem literalEntries_split (start : Nat) (ls : List (PeriodicLiteral Nat))
    {p : Nat} {l : PeriodicLiteral Nat} (h : (p,l) ∈ literalEntries start ls) :
    ∃ pre post, ls.flatMap literalFields = pre++literalFields l++post ∧ p=start+pre.length := by
  induction ls generalizing start with
  | nil => simp [literalEntries] at h
  | cons first rest ih =>
    simp only [literalEntries,List.mem_cons,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | h
    · exact ⟨[],rest.flatMap literalFields,by simp,by simp⟩
    · obtain ⟨pre,post,he,hp⟩ := ih (start+4) h
      refine ⟨literalFields first++pre,post,?_,?_⟩
      · simp [he,List.append_assoc]
      · simp only [List.length_append,literalFields,List.length_cons,List.length_nil]
        omega

theorem clauseEntries_split (start : Nat) (cs : List (PeriodicClause Nat))
    {p : Nat} {c : PeriodicClause Nat} (h : (p,c) ∈ clauseEntries start cs) :
    ∃ pre post, cs.flatMap clauseFields = pre++clauseFields c++post ∧ p=start+pre.length := by
  induction cs generalizing start with
  | nil => simp [clauseEntries] at h
  | cons first rest ih =>
    simp only [clauseEntries,List.mem_cons,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | h
    · exact ⟨[],rest.flatMap clauseFields,by simp,by simp⟩
    · obtain ⟨pre,post,he,hp⟩ := ih (start+1+4*first.length) h
      refine ⟨clauseFields first++pre,post,?_,?_⟩
      · simp [he,List.append_assoc]
      · simp only [List.length_append,clauseFields,List.length_cons,flat_literal_length]
        omega

theorem allLiteralEntries_split (start : Nat) (cs : List (PeriodicClause Nat))
    {p : Nat} {l : PeriodicLiteral Nat} (h : (p,l) ∈ allLiteralEntries start cs) :
    ∃ pre post, cs.flatMap clauseFields = pre++literalFields l++post ∧ p=start+pre.length := by
  induction cs generalizing start with
  | nil => simp [allLiteralEntries] at h
  | cons c cs ih =>
    simp only [allLiteralEntries,List.mem_append] at h
    rcases h with h | h
    · obtain ⟨pre,post,he,hp⟩ := literalEntries_split (start+1) c h
      refine ⟨c.length::pre,post++cs.flatMap clauseFields,?_,?_⟩
      · simp [clauseFields,he,List.append_assoc]
      · simp only [List.length_cons]; omega
    · obtain ⟨pre,post,he,hp⟩ := ih (start+1+4*c.length) h
      refine ⟨clauseFields c++pre,post,?_,?_⟩
      · simp [he,List.append_assoc]
      · simp only [List.length_append,clauseFields,List.length_cons,flat_literal_length]
        omega

theorem literalEntries_members (start : Nat) (ls : List (PeriodicLiteral Nat)) (l : PeriodicLiteral Nat) :
    (∃ p, (p,l) ∈ literalEntries start ls) ↔ l ∈ ls := by
  induction ls generalizing start with
  | nil => simp [literalEntries]
  | cons first rest ih => simp [literalEntries,ih,Prod.mk.injEq,exists_or]

theorem clauseEntries_members (start : Nat) (cs : List (PeriodicClause Nat)) (c : PeriodicClause Nat) :
    (∃ p, (p,c) ∈ clauseEntries start cs) ↔ c ∈ cs := by
  induction cs generalizing start with
  | nil => simp [clauseEntries]
  | cons first rest ih => simp [clauseEntries,ih,Prod.mk.injEq,exists_or]

theorem allLiteralEntries_members (start : Nat) (cs : List (PeriodicClause Nat)) (l : PeriodicLiteral Nat) :
    (∃ p, (p,l) ∈ allLiteralEntries start cs) ↔ ∃ c ∈ cs, l ∈ c := by
  induction cs generalizing start with
  | nil => simp [allLiteralEntries]
  | cons c cs ih => simp [allLiteralEntries,exists_or,literalEntries_members,ih]

theorem literalEntry_atom (f : PeriodicCNF Nat) {p : Nat} {l : PeriodicLiteral Nat}
    (h : (p,l) ∈ allLiteralEntries 1 f.clauses) :
    (formulaFields f)[p]?.getD 0 = l.atom := by
  obtain ⟨pre,post,he,rfl⟩ := allLiteralEntries_split 1 f.clauses h
  simp only [formulaFields,he]
  rw [show 1+pre.length = pre.length+1 by omega,List.getElem?_cons_succ]
  rw [List.append_assoc,List.getElem?_append_right (by omega),Nat.sub_self]
  simp [literalFields]

end LeanTrominoes.PeriodicCNF.FlatScanner
