/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMLineWindow
import LeanTrominoes.PeriodicThreeDMDegreeWitnesses

/-! # Exactly one selected incidence as a unique bounded triple index -/
namespace LeanTrominoes.PeriodicThreeDM.LineWindow
open Gadget

def indexValue (p : PeriodicThreeDM) (color : WireColor) (word index : Nat) : Bool :=
  word.testBit (index+p.triples.length*(position ⟨index,((p.triples.getD index default).reference color).offset⟩).val)

def Selected (p : PeriodicThreeDM) (color : WireColor) (atom word index : Nat) : Prop :=
  incidentIndex p color atom index ∧ indexValue p color word index = true
instance (p : PeriodicThreeDM) (color : WireColor) (atom word index : Nat) :
    Decidable (Selected p color atom word index) := by unfold Selected; infer_instance

def selectedIndices (p : PeriodicThreeDM) (color : WireColor) (atom word : Nat) : Finset Nat :=
  ((List.range p.triples.length).filter (fun j => decide (Selected p color atom word j))).toFinset

theorem mem_selectedIndices (p : PeriodicThreeDM) (color : WireColor) (atom word j : Nat) :
    j ∈ selectedIndices p color atom word ↔ j < p.triples.length ∧ Selected p color atom word j := by
  simp [selectedIndices]

theorem incidence_value (p : PeriodicThreeDM) (color : WireColor) (atom word : Nat)
    {i : Incidence} (hi : i ∈ p.incidences color atom) :
    value p i.tripleIndex (decodeWord p word (position i)) = indexValue p color word i.tripleIndex := by
  have bound := incidence_tripleIndex_lt p color atom hi
  have offset : ((p.triples.getD i.tripleIndex default).reference color).offset = i.offset := by
    simp only [incidences,List.mem_filterMap] at hi
    obtain ⟨j,_,h⟩ := hi
    split at h
    · simp only [Option.some.injEq] at h
      subst i
      rfl
    · contradiction
  simp only [value,dif_pos bound,decodeWord,indexValue,offset]
  rfl

theorem selected_card (p : PeriodicThreeDM) (color : WireColor) (atom word : Nat) :
    ((p.incidences color atom).map (fun i => value p i.tripleIndex (decodeWord p word (position i)))).count true =
      (selectedIndices p color atom word).card := by
  have mapped : (p.incidences color atom).map (fun i => value p i.tripleIndex (decodeWord p word (position i))) =
      (p.incidences color atom).map (fun i => indexValue p color word i.tripleIndex) := by
    apply List.map_congr_left
    intro i hi
    exact incidence_value p color atom word hi
  rw [mapped,selectedIndices,List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  have helper (indices : List Nat) :
      ((indices.filterMap (fun j => if incidentIndex p color atom j then
        some (⟨j,((p.triples.getD j default).reference color).offset⟩ : Incidence) else none)).map
        (fun i => indexValue p color word i.tripleIndex)).count true =
      (indices.filter (fun j => decide (Selected p color atom word j))).length := by
    induction indices with
    | nil => rfl
    | cons j rest ih =>
      by_cases h : incidentIndex p color atom j <;>
        cases hv : indexValue p color word j <;>
        simpa [Selected,h,hv] using ih
  exact helper _

theorem exactlyOne_iff_unique (p : PeriodicThreeDM) (color : WireColor) (atom word : Nat) :
    PeriodicOneInThree.ExactlyOne
      ((p.incidences color atom).map fun i => value p i.tripleIndex (decodeWord p word (position i))) ↔
      ∃ j < p.triples.length, Selected p color atom word j ∧
        ∀ k < p.triples.length, Selected p color atom word k → k=j := by
  rw [PeriodicOneInThree.ExactlyOne,selected_card,Finset.card_eq_one]
  constructor
  · rintro ⟨j,hj⟩
    have member : j ∈ selectedIndices p color atom word := by rw [hj]; simp
    obtain ⟨bound,selected⟩ := (mem_selectedIndices p color atom word j).mp member
    refine ⟨j,bound,selected,?_⟩
    intro k hk sk
    have member := (mem_selectedIndices p color atom word k).mpr ⟨hk,sk⟩
    simpa only [hj,Finset.mem_singleton] using member
  · rintro ⟨j,hj,sj,unique⟩
    refine ⟨j,?_⟩
    ext k
    rw [mem_selectedIndices,Finset.mem_singleton]
    constructor
    · rintro ⟨hk,sk⟩; exact unique k hk sk
    · rintro rfl; exact ⟨hj,sj⟩

end LeanTrominoes.PeriodicThreeDM.LineWindow
