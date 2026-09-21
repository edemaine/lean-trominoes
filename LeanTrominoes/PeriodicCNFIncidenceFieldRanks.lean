/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFIncidenceFieldCount
import LeanTrominoes.BoundedArithmeticCountAddresses
import LeanTrominoes.ListSortedAddressRank

/-! # Native field counts recover incidence vertex indices -/
namespace LeanTrominoes.PeriodicCNF.IncidenceFields
open FlatScanner FieldPredicate PeriodicCNFFlatEncoding LastOccurrenceEntries
open BoundedArithmetic BoundedArithmetic.Expr

theorem representative_bound (f : PeriodicCNF Nat) (p : Nat) (h : representative f p) :
    p < (formulaFields f).length := by
  obtain ⟨l,hl⟩ := (literalMarks_testBit _ _ _).mp h.1
  exact literal_bound f hl

theorem representatives_sorted (f : PeriodicCNF Nat) :
    ((representatives f).map Prod.fst).SortedLT :=
  List.sortedLT_iff_pairwise.mpr ((entries_sorted f).pairwise.sublist
    ((List.filter_sublist (l := entries f)).map Prod.fst))

theorem representative_rank_count (f : PeriodicCNF Nat) (p : Nat) :
    Count.count representativeExpr (FieldSavitch.suffix f) p =
      ((representatives f).filter fun e => decide (e.1<p)).length := by
  have h := Count.count_addresses representativeExpr (FieldSavitch.suffix f) p
    ((representatives f).map Prod.fst) (representatives_addresses_nodup f) (fun q => by
      rw [mem_representatives,representativeExpr_truth]
      exact ⟨And.right,fun h => ⟨representative_bound f q h,h⟩⟩)
  simpa only [List.filter_map,List.length_map,Function.comp_def] using h

theorem representative_rank (f : PeriodicCNF Nat) (p : Nat) (h : representative f p) :
    f.variableOccurrences.dedup.idxOf ((formulaFields f)[p]?.getD 0) =
      Count.count representativeExpr (FieldSavitch.suffix f) p := by
  rw [representative_rank_count,← representatives_atoms]
  have member : (p,(formulaFields f)[p]?.getD 0) ∈ representatives f := by
    obtain ⟨⟨q,a⟩,he,hq⟩ := List.mem_map.mp ((mem_representatives f p).mpr ⟨representative_bound f p h,h⟩)
    have qp : q=p := hq
    subst q
    have hm := (mem_entries f p a).mp (List.mem_filter.mp he).1
    simpa only [hm.2.2] using he
  apply SortedAddressRank.idxOf_eq_before _ (representatives_sorted f) _ p _ member
  rw [representatives_atoms]
  exact List.nodup_dedup _

def clauseMarkExpr : Expr := .testBit (var 2) (var 0)
def literalMarkExpr : Expr := .testBit (var 3) (var 0)

theorem clauseMarkExpr_truth (f : PeriodicCNF Nat) (p : Nat) :
    clauseMarkExpr.Truth (p::FieldSavitch.suffix f) ↔
      p ∈ (clauseEntries 1 f.clauses).map Prod.fst := by
  simp only [clauseMarkExpr,truth_bit,FieldSavitch.suffix,input,context,List.cons_append,List.nil_append,
    eval_var,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,clauseMarks_testBit,List.mem_map]
  constructor
  · rintro ⟨c,hc⟩; exact ⟨(p,c),hc,rfl⟩
  · rintro ⟨⟨q,c⟩,hc,rfl⟩; exact ⟨c,hc⟩

theorem literalMarkExpr_truth (f : PeriodicCNF Nat) (p : Nat) :
    literalMarkExpr.Truth (p::FieldSavitch.suffix f) ↔
      p ∈ (allLiteralEntries 1 f.clauses).map Prod.fst := by
  simp only [literalMarkExpr,truth_bit,FieldSavitch.suffix,input,context,List.cons_append,List.nil_append,
    eval_var,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,literalMarks_testBit,List.mem_map]
  constructor
  · rintro ⟨l,hl⟩; exact ⟨(p,l),hl,rfl⟩
  · rintro ⟨⟨q,l⟩,hl,rfl⟩; exact ⟨l,hl⟩

theorem clause_rank_count (f : PeriodicCNF Nat) (p : Nat) :
    Count.count clauseMarkExpr (FieldSavitch.suffix f) p =
      ((clauseEntries 1 f.clauses).filter fun e => decide (e.1<p)).length := by
  have h := Count.count_addresses clauseMarkExpr (FieldSavitch.suffix f) p
    ((clauseEntries 1 f.clauses).map Prod.fst) (clauseEntries_sorted _ _).nodup
    (fun q => (clauseMarkExpr_truth f q).symm)
  simpa only [List.filter_map,List.length_map,Function.comp_def] using h

theorem literal_rank_count (f : PeriodicCNF Nat) (p : Nat) :
    Count.count literalMarkExpr (FieldSavitch.suffix f) p =
      ((allLiteralEntries 1 f.clauses).filter fun e => decide (e.1<p)).length := by
  have h := Count.count_addresses literalMarkExpr (FieldSavitch.suffix f) p
    ((allLiteralEntries 1 f.clauses).map Prod.fst) (allLiteralEntries_sorted _ _).nodup
    (fun q => (literalMarkExpr_truth f q).symm)
  simpa only [List.filter_map,List.length_map,Function.comp_def] using h

end LeanTrominoes.PeriodicCNF.IncidenceFields
