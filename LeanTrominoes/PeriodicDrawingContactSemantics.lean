/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingContactProgram

/-! # The contact program checks precisely the finite endpoint certificate -/
namespace LeanTrominoes.PeriodicGridDrawing.ContactProgram
open BoundedArithmetic BoundedArithmetic.Expr NativeRoutes Arithmetic

theorem program_indexed (d : PeriodicGridDrawing) (front rest : List Nat) :
    (program front.length).value (front++fields d++rest) ≠ 0 ↔
      ∀ i (hi : i<d.edgeRoutes.length), ∀ j (hj : j<d.edgeRoutes[i].length),
      ∀ k (hk : k<d.edgeRoutes.length), ∀ l (hl : l<d.edgeRoutes[k].length),
      ∀ (x : Nat), x < 5 → ∀ (y : Nat), y < 5 →
        Contact d (d.routePointAt i hi j hj) (d.routePointAt k hk l hl) ((x:Int)-2,(y:Int)-2) := by
  rw [program,allPoints_truth]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  have inner := allPoints_truth d (pointContext d front i j) rest (translations front.length)
  change ((allPoints (front.length+3) (translations front.length)).value
    (j::address d (i::front) i::i::(front++fields d++rest)) ≠ 0) ↔ _ at inner
  apply inner.trans
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  rw [translations,NativeScalar.all_value_ne_zero]
  change (∀ (x : Nat), x < 5 → (NativeScalar.all _ _).value (x::l::address d (k::pointContext d front i j) k::k::
    (pointContext d front i j++fields d++rest)) ≠ 0) ↔ _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  rw [NativeScalar.all_value_ne_zero]
  change (∀ (y : Nat), y < 5 → (body front.length).Truth
    (y::x::pointContext d (pointContext d front i j) k l++fields d++rest)) ↔ _
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  exact body_truth d front rest i hi j hj k hk l hl x y

private theorem translations_iff (P : Cell → Prop) :
    (∀ (x : Nat), x < 5 → ∀ (y : Nat), y < 5 → P ((x:Int)-2,(y:Int)-2)) ↔ ∀ t ∈ doubleNeighborTranslations, P t := by
  constructor
  · intro h t ht
    have bounds := (mem_doubleNeighborTranslations_iff t).mp ht
    have hx : (t.1+2).toNat < 5 := by omega
    have hy : (t.2+2).toNat < 5 := by omega
    have eq : (((t.1+2).toNat:Int)-2,((t.2+2).toNat:Int)-2)=t := by
      apply Prod.ext <;> dsimp only <;> omega
    simpa only [eq] using h (t.1+2).toNat hx (t.2+2).toNat hy
  · intro h x hx y hy
    apply h _ ((mem_doubleNeighborTranslations_iff _).mpr ?_)
    dsimp only
    omega

theorem program_correct (d : PeriodicGridDrawing) (front rest : List Nat) :
    (program front.length).value (front++fields d++rest) ≠ 0 ↔
      d.expandedFiniteRoutePointsMeetOnlyAtEndpoints = true := by
  rw [program_indexed]
  simp only [expandedFiniteRoutePointsMeetOnlyAtEndpoints,List.all_eq_true,decide_eq_true_eq]
  change _ ↔ ∀ first ∈ d.indexedRoutePoints, ∀ second ∈ d.indexedRoutePoints,
    ∀ relative ∈ doubleNeighborTranslations, Contact d first second relative
  rw [forall_indexedRoutePoints_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [forall_indexedRoutePoints_iff]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  exact translations_iff _

end LeanTrominoes.PeriodicGridDrawing.ContactProgram
