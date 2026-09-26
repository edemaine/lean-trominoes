/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFieldQueries
import LeanTrominoes.PeriodicThreeDMLineDecision

/-! # Native field checks for well-formed horizontal local 3DM -/
namespace LeanTrominoes.PeriodicThreeDM.CoreGuard
open Gadget FlatEncoding FieldQueries BoundedArithmetic BoundedArithmetic.Expr

def referenceCheck (color : WireColor) : Expr :=
  andE (ltE (entry 1 (var 0) color 0) (var (1+colorIndex color)))
    (andE (leE (entry 1 (var 0) color 1) 2) (eqE (entry 1 (var 0) color 2) 0))

def core : Expr := .all (var 3)
  (andE (referenceCheck .red) (andE (referenceCheck .green) (referenceCheck .blue)))

private theorem signed_small (z : Int) : Encodable.encode z ≤ 2 ↔ z.natAbs ≤ 1 := by
  cases z with
  | ofNat n => change 2*n ≤ 2 ↔ n ≤ 1; omega
  | negSucc n => change 2*n+1 ≤ 2 ↔ n+1 ≤ 1; omega

private theorem signed_zero (z : Int) : Encodable.encode z = 0 ↔ z = 0 := by
  change Encodable.encode z = Encodable.encode (0:Int) ↔ z = 0
  exact Encodable.encode_injective.eq_iff

theorem referenceCheck_truth (p : PeriodicThreeDM) (i : Nat) (hi : i < p.triples.length)
    (color : WireColor) : (referenceCheck color).Truth (i::fields p) ↔
      (p.triples[i].reference color).atom < p.elementCount color ∧
      (p.triples[i].reference color).offset.1.natAbs ≤ 1 ∧
      (p.triples[i].reference color).offset.2 = 0 := by
  have entryAt (k : Fin 3) := entry_eval p [i] (var 0) color k hi
  change ∀ k : Fin 3, (entry 1 (var 0) color k).eval (i::fields p) =
    (referenceFields (p.triples[i].reference color))[k.val]?.getD 0 at entryAt
  have countAt := count_eval p [i] color
  change (var (1+colorIndex color)).eval (i::fields p) = p.elementCount color at countAt
  simp only [referenceCheck,truth_and,truth_lt,truth_le,truth_eq]
  rw [entryAt 0,entryAt 1,entryAt 2,countAt]
  change ((p.triples[i].reference color).atom < p.elementCount color ∧
    Encodable.encode (p.triples[i].reference color).offset.1 ≤ 2 ∧
    Encodable.encode (p.triples[i].reference color).offset.2 = 0) ↔ _
  rw [signed_small,signed_zero]

theorem core_truth (p : PeriodicThreeDM) : core.Truth (fields p) ↔
    p.IsWellFormed ∧ p.IsOneDimensional ∧ p.IsLocal := by
  simp only [core,truth_all,truth_and]
  change (∀ i < p.triples.length, (referenceCheck .red).Truth (i::fields p) ∧
    (referenceCheck .green).Truth (i::fields p) ∧ (referenceCheck .blue).Truth (i::fields p)) ↔ _
  have colors (i : Nat) (hi : i < p.triples.length) :
      ((referenceCheck .red).Truth (i::fields p) ∧ (referenceCheck .green).Truth (i::fields p) ∧
      (referenceCheck .blue).Truth (i::fields p)) ↔
      ∀ c, (p.triples[i].reference c).atom < p.elementCount c ∧
        (p.triples[i].reference c).offset.1.natAbs ≤ 1 ∧ (p.triples[i].reference c).offset.2 = 0 := by
    rw [referenceCheck_truth p i hi .red,referenceCheck_truth p i hi .green,referenceCheck_truth p i hi .blue]
    constructor
    · intro h c; cases c <;> tauto
    · intro h; exact ⟨h .red,h .green,h .blue⟩
  refine (forall_congr' (fun i => forall_congr' (fun hi => colors i hi))).trans ?_
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro t ht c
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ht
      exact (h i hi c).1
    · intro t ht c
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ht
      exact (h i hi c).2.2
    · intro t ht c
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ht
      have hc := h i hi c
      simpa only [hc.2.2,Int.natAbs_zero,Nat.add_zero] using hc.2.1
  · rintro ⟨wf,horizontal,locality⟩ i hi c
    have member := List.getElem_mem hi
    have hz := horizontal _ member c
    refine ⟨wf _ member c,?_,hz⟩
    have bound := locality _ member c
    simpa only [hz,Int.natAbs_zero,Nat.add_zero] using bound

theorem core_noPower : core.noPower = true := by
  simp [core,referenceCheck,entry,andE,ltE,leE,notE,eqE,var,Expr.noPower]

end LeanTrominoes.PeriodicThreeDM.CoreGuard
