/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDM
import LeanTrominoes.FiniteSetDegreeTwoThree

/-! # Bounded index witnesses for the colored degree restriction -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

def incidentIndex (p : PeriodicThreeDM) (color : WireColor) (atom index : Nat) : Prop :=
  ((p.triples.getD index default).reference color).atom = atom
instance (p : PeriodicThreeDM) (color : WireColor) (atom index : Nat) :
    Decidable (incidentIndex p color atom index) := inferInstanceAs (Decidable (_ = _))

def incidentIndices (p : PeriodicThreeDM) (color : WireColor) (atom : Nat) : Finset Nat :=
  ((List.range p.triples.length).filter (fun i => decide (incidentIndex p color atom i))).toFinset

theorem mem_incidentIndices (p : PeriodicThreeDM) (color : WireColor) (atom index : Nat) :
    index ∈ incidentIndices p color atom ↔ index < p.triples.length ∧ incidentIndex p color atom index := by
  simp [incidentIndices]

theorem degree_eq_card (p : PeriodicThreeDM) (color : WireColor) (atom : Nat) :
    p.degree color atom = (incidentIndices p color atom).card := by
  have lengths (indices : List Nat) :
      (indices.filterMap (fun j => if incidentIndex p color atom j then
        some (⟨j,((p.triples.getD j default).reference color).offset⟩ : Incidence) else none)).length =
      (indices.filter (fun j => decide (incidentIndex p color atom j))).length := by
    induction indices with
    | nil => rfl
    | cons j rest ih =>
      by_cases h : incidentIndex p color atom j <;> simpa [h] using ih
  rw [incidentIndices,List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  exact lengths _

def DegreeWitnesses (p : PeriodicThreeDM) (color : WireColor) (atom : Nat) : Prop :=
  ∃ a < p.triples.length, ∃ b < p.triples.length, ∃ c < p.triples.length,
    a ≠ b ∧ incidentIndex p color atom a ∧ incidentIndex p color atom b ∧
    incidentIndex p color atom c ∧ ∀ j < p.triples.length,
      incidentIndex p color atom j → j = a ∨ j = b ∨ j = c

theorem degree_witnesses_iff (p : PeriodicThreeDM) (color : WireColor) (atom : Nat) :
    DegreeWitnesses p color atom ↔ p.degree color atom ∈ ([2,3] : List Nat) := by
  rw [degree_eq_card]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rw [finset_card_two_or_three_iff]
  simp only [mem_incidentIndices,DegreeWitnesses]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,hab,ia,ib,ic,cover⟩
    exact ⟨a,⟨ha,ia⟩,b,⟨hb,ib⟩,c,⟨hc,ic⟩,hab,fun j hj => cover j hj.1 hj.2⟩
  · rintro ⟨a,⟨ha,ia⟩,b,⟨hb,ib⟩,c,⟨hc,ic⟩,hab,cover⟩
    exact ⟨a,ha,b,hb,c,hc,hab,ia,ib,ic,fun j hj ij => cover j ⟨hj,ij⟩⟩

end LeanTrominoes.PeriodicThreeDM
