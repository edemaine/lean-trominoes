/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Orientation.TrichromaticGraphOrientationFieldTransition

/-! # Bounded endpoint and offset checks for native orientation instances -/
namespace LeanTrominoes.TrichromaticGraphOrientation.CoreGuard
open FlatEncoding FieldQueries BoundedArithmetic BoundedArithmetic.Expr

def recordCheck : Expr := andE (ltE (entry 6 (var 0) 0) (var 6))
  (andE (ltE (entry 6 (var 0) 1) (var 6))
    (andE (leE (entry 6 (var 0) 2) 2) (eqE (entry 6 (var 0) 3) 0)))
def core : Expr := .all (var 0) recordCheck

private theorem signed_small (z : Int) : Encodable.encode z ≤ 2 ↔ z.natAbs ≤ 1 := by
  cases z with
  | ofNat n => change 2*n ≤ 2 ↔ n ≤ 1; omega
  | negSucc n => change 2*n+1 ≤ 2 ↔ n+1 ≤ 1; omega

private theorem signed_zero (z : Int) : Encodable.encode z = 0 ↔ z = 0 := by
  change Encodable.encode z = Encodable.encode (0:Int) ↔ z = 0
  exact Encodable.encode_injective.eq_iff

theorem recordCheck_truth (graph : Input) (index : Nat) (bound : index < graph.2.length) :
    recordCheck.Truth (index::FieldPredicate.input graph 0 0) ↔
      graph.2[index].1.source < graph.1.length ∧ graph.2[index].1.target < graph.1.length ∧
      graph.2[index].1.offset.1.natAbs ≤ 1 ∧ graph.2[index].1.offset.2 = 0 := by
  have entryAt (field : Fin 5) := entry_eval graph [index,graph.2.length,0,0,0,0] (var 0) field bound
  change ∀ field : Fin 5, (entry 6 (var 0) field).eval (index::FieldPredicate.input graph 0 0) =
    (edgeFields graph.2[index])[field.val]?.getD 0 at entryAt
  have count := vertexCount_eval graph [index,graph.2.length,0,0,0,0]
  change (var 6).eval (index::FieldPredicate.input graph 0 0) = graph.1.length at count
  simp only [recordCheck,truth_and,truth_lt,truth_le,truth_eq]
  rw [entryAt 0,entryAt 1,entryAt 2,entryAt 3,count]
  change (graph.2[index].1.source < graph.1.length ∧ graph.2[index].1.target < graph.1.length ∧
    Encodable.encode graph.2[index].1.offset.1 ≤ 2 ∧ Encodable.encode graph.2[index].1.offset.2 = 0) ↔ _
  rw [signed_small,signed_zero]

theorem core_truth (graph : Input) : core.Truth (FieldPredicate.input graph 0 0) ↔
    (∀ record ∈ graph.2, record.1.source < graph.1.length ∧ record.1.target < graph.1.length) ∧
      IsOneDimensional graph ∧ IsLocal graph := by
  rw [core,truth_all]
  change (∀ index < graph.2.length, recordCheck.Truth (index::FieldPredicate.input graph 0 0)) ↔ _
  refine (forall_congr' (fun index => forall_congr' (fun bound => recordCheck_truth graph index bound))).trans ?_
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro record member
      obtain ⟨index,bound,rfl⟩ := List.mem_iff_getElem.mp member
      exact ⟨(h index bound).1,(h index bound).2.1⟩
    · intro record member
      obtain ⟨index,bound,rfl⟩ := List.mem_iff_getElem.mp member
      exact (h index bound).2.2.2
    · intro record member
      obtain ⟨index,bound,rfl⟩ := List.mem_iff_getElem.mp member
      simpa only [PeriodicEdge.span,(h index bound).2.2.2,Int.natAbs_zero,Nat.add_zero] using
        (h index bound).2.2.1
  · rintro ⟨endpoints,horizontal,locality⟩ index bound
    have member := List.getElem_mem bound
    have zero := horizontal _ member
    refine ⟨(endpoints _ member).1,(endpoints _ member).2,?_,zero⟩
    simpa only [PeriodicEdge.span,zero,Int.natAbs_zero,Nat.add_zero] using locality _ member

theorem core_noPower : core.noPower = true := by
  simp [core,recordCheck,entry,andE,ltE,leE,notE,eqE,var,Expr.noPower]

end LeanTrominoes.TrichromaticGraphOrientation.CoreGuard
