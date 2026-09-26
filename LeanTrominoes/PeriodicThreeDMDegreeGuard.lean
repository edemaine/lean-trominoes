/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFieldQueries
import LeanTrominoes.PeriodicThreeDMDegreeWitnesses

/-! # An arithmetic guard for degree two or three in every color -/
namespace LeanTrominoes.PeriodicThreeDM.DegreeGuard
open Gadget FlatEncoding FieldQueries BoundedArithmetic BoundedArithmetic.Expr

def matchEntry (depth : Nat) (color : WireColor) (index atom : Expr) : Expr :=
  eqE (entry depth index color 0) atom

theorem matchEntry_truth (p : PeriodicThreeDM) (front : List Nat) (color : WireColor)
    (index atom : Expr) (hi : index.eval (front++fields p) < p.triples.length) :
    (matchEntry front.length color index atom).Truth (front++fields p) ↔
      incidentIndex p color (atom.eval (front++fields p)) (index.eval (front++fields p)) := by
  rw [matchEntry,truth_eq,entry_eval p front index color 0 hi]
  simp only [referenceFields,Fin.val_zero,List.getElem?_cons_zero,Option.getD_some,incidentIndex,
    List.getD_eq_getElem _ _ hi]

-- Witness context: c, b, a, element, then the native instance fields.
def witnesses (color : WireColor) : Expr :=
  andE (notE (eqE (var 2) (var 1)))
    (andE (matchEntry 4 color (var 2) (var 3))
      (andE (matchEntry 4 color (var 1) (var 3))
        (andE (matchEntry 4 color (var 0) (var 3))
          (.all (var 7) (impE (matchEntry 5 color (var 0) (var 4))
            (orE (eqE (var 0) (var 3))
              (orE (eqE (var 0) (var 2)) (eqE (var 0) (var 1)))))))))

def element (color : WireColor) : Expr :=
  existsE (var 4) (existsE (var 5) (existsE (var 6) (witnesses color)))

def colorCheck (color : WireColor) : Expr := .all (var (colorIndex color)) (element color)
def guard : Expr := andE (colorCheck .red) (andE (colorCheck .green) (colorCheck .blue))

theorem witnesses_truth (p : PeriodicThreeDM) (color : WireColor) (v a b c : Nat)
    (ha : a < p.triples.length) (hb : b < p.triples.length) (hc : c < p.triples.length) :
    (witnesses color).Truth (c::b::a::v::fields p) ↔
      a ≠ b ∧ incidentIndex p color v a ∧ incidentIndex p color v b ∧ incidentIndex p color v c ∧
      ∀ j < p.triples.length, incidentIndex p color v j → j=a ∨ j=b ∨ j=c := by
  have atA := matchEntry_truth p [c,b,a,v] color (var 2) (var 3) ha
  have atB := matchEntry_truth p [c,b,a,v] color (var 1) (var 3) hb
  have atC := matchEntry_truth p [c,b,a,v] color (var 0) (var 3) hc
  change (matchEntry 4 color (var 2) (var 3)).Truth (c::b::a::v::fields p) ↔ incidentIndex p color v a at atA
  change (matchEntry 4 color (var 1) (var 3)).Truth (c::b::a::v::fields p) ↔ incidentIndex p color v b at atB
  change (matchEntry 4 color (var 0) (var 3)).Truth (c::b::a::v::fields p) ↔ incidentIndex p color v c at atC
  simp only [witnesses,truth_and,truth_not,truth_eq,truth_all,truth_imp,truth_or,atA,atB,atC]
  change (a ≠ b ∧ incidentIndex p color v a ∧ incidentIndex p color v b ∧ incidentIndex p color v c ∧
    ∀ j < p.triples.length, (matchEntry 5 color (var 0) (var 4)).Truth (j::c::b::a::v::fields p) →
      j=a ∨ j=b ∨ j=c) ↔ _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  have atJ := matchEntry_truth p [j,c,b,a,v] color (var 0) (var 4) hj
  change (matchEntry 5 color (var 0) (var 4)).Truth (j::c::b::a::v::fields p) ↔ incidentIndex p color v j at atJ
  rw [atJ]

theorem element_truth (p : PeriodicThreeDM) (color : WireColor) (v : Nat) :
    (element color).Truth (v::fields p) ↔ p.degree color v ∈ ([2,3] : List Nat) := by
  rw [← degree_witnesses_iff]
  simp only [element,truth_exists]
  change (∃ a < p.triples.length, ∃ b < p.triples.length, ∃ c < p.triples.length,
    (witnesses color).Truth (c::b::a::v::fields p)) ↔ _
  unfold DegreeWitnesses
  apply exists_congr
  intro a
  apply and_congr_right
  intro ha
  apply exists_congr
  intro b
  apply and_congr_right
  intro hb
  apply exists_congr
  intro c
  apply and_congr_right
  intro hc
  exact witnesses_truth p color v a b c ha hb hc

theorem colorCheck_truth (p : PeriodicThreeDM) (color : WireColor) :
    (colorCheck color).Truth (fields p) ↔
      ∀ v < p.elementCount color, p.degree color v ∈ ([2,3] : List Nat) := by
  rw [colorCheck,truth_all]
  have count := count_eval p [] color
  simp only [List.length_nil,List.nil_append,Nat.zero_add] at count
  rw [count]
  simp only [element_truth]

theorem guard_truth (p : PeriodicThreeDM) : guard.Truth (fields p) ↔ p.DegreeTwoOrThree := by
  simp only [guard,truth_and,colorCheck_truth,DegreeTwoOrThree]
  constructor
  · intro h color; cases color <;> tauto
  · intro h; exact ⟨h .red,h .green,h .blue⟩

theorem guard_noPower : guard.noPower = true := by
  simp [guard,colorCheck,element,witnesses,matchEntry,entry,existsE,notE,eqE,orE,andE,impE,var,Expr.noPower]

end LeanTrominoes.PeriodicThreeDM.DegreeGuard
