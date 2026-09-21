/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteLeafSemantics

/-! # Recovering the variable endpoint from its last literal occurrence -/
namespace LeanTrominoes.PeriodicCNF.IncidenceFields
open PeriodicCNFFlatEncoding

theorem representative_exists (f : PeriodicCNF Nat) (a : Nat) (ha : a∈f.variableOccurrences.dedup) :
    ∃ r, representative f r ∧ (formulaFields f)[r]?.getD 0=a := by
  rw [← representatives_atoms] at ha
  obtain ⟨⟨r,b⟩,hm,eq⟩ := List.mem_map.mp ha
  have ba : b=a := eq
  subst b
  refine ⟨r,?_,?_⟩
  · exact ((mem_representatives f r).mp (List.mem_map.mpr ⟨(r,a),hm,rfl⟩)).2
  · exact ((mem_entries f r a).mp (List.mem_filter.mp hm).1).2.2

end LeanTrominoes.PeriodicCNF.IncidenceFields

namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open BoundedArithmetic BoundedArithmetic.Expr BoundedArithmetic.SignedGeometry
open RouteInput PeriodicCNF.FlatScanner PeriodicCNF.IncidenceFields PeriodicCNFFlatEncoding

theorem targetRank_value (input : Input Nat) (r e k ci h v : Nat)
    (hr : representative input.1 r) :
    targetRank.value ([r,e,k,ci,h,v]++context input) =
      input.1.variableOccurrences.dedup.idxOf ((formulaFields input.1)[r]?.getD 0) := by
  change Count.count (formulaQuery 6 representativeExpr) ([r,e,k,ci,h,v]++context input) r = _
  have count := formulaQuery_count representativeExpr input [r,e,k,ci,h,v] r
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd] at count
  rw [count]
  exact (representative_rank input.1 r hr).symm

theorem representativeGuard_truth (input : Input Nat) (r e k ci h v : Nat)
    (c : PeriodicClause Nat) (hc : (h,c)∈clauseEntries 1 input.1.clauses) (hk : k<c.length) :
    representativeGuard.Truth ([r,e,k,ci,h,v]++context input) ↔
      representative input.1 r ∧ (formulaFields input.1)[r]?.getD 0 = c[k].atom := by
  have rep := formulaQuery_eval representativeExpr input [e,k,ci,h,v] r
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,List.cons_append,List.nil_append] at rep
  have a := formulaField_eval input [r,e,k,ci,h,v] (var 0)
  have b := formulaField_eval input [r,e,k,ci,h,v] (var 4+1+4*var 2)
  change (formulaField 6 (var 0)).eval _ = (formulaFields input.1)[r]?.getD 0 at a
  change (formulaField 6 (var 4+1+4*var 2)).eval _ = (formulaFields input.1)[h+1+4*k]?.getD 0 at b
  rw [representativeGuard,truth_and,truth_eq,a,b,PeriodicCNF.FieldPredicate.clause_atom input.1 hc k hk]
  change (formulaQuery 5 representativeExpr).eval _ ≠ 0 ∧ _ ↔ _
  simp only [List.cons_append,List.nil_append]
  rw [rep]
  exact and_congr (representativeExpr_truth input.1 r) Iff.rfl

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
