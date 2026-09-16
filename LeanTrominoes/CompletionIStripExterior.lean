/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIStripStates
import LeanTrominoes.TrominoCompletionUnion

/-! # Restoring blank exterior bricks around a completed core -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

def exteriorPrescribed (palette : Cell → Fin 24) (count : Int) : Set (Finset Cell) :=
  {f | ∃ o : Occurrence palette, ¬ InBand count o.location ∧ f ∈ atomPrescribed o.location o.entry}

theorem exterior_completion (palette : Cell → Fin 24) (count : Int) (hn : 0 < count)
    (blank : ∀ location, ¬ InBand count location → palette location = 0) :
    Tromino.I.Completable (StripCaps.coreBand .I (162*count))ᶜ (exteriorPrescribed palette count) := by
  let Selected := {o : Occurrence palette // ¬ InBand count o.location}
  have localCompletion (o : Selected) := state_completion o.val (booleanOutside (fun _ => false) o.val)
    (blank_state_realized palette o.val (blank o.val.location o.property))
  have separate (a b : Selected) (c : Cell)
      (ha : c ∈ stateTarget a.val (booleanOutside (fun _ => false) a.val))
      (hb : c ∈ stateTarget b.val (booleanOutside (fun _ => false) b.val)) : a = b := by
    rw [boolean_state_target] at ha hb
    obtain ⟨chosen,_,unique⟩ := boolean_groups_partition palette (fun _ => false) c
    exact Subtype.ext ((unique a.val ha).trans (unique b.val hb).symm)
  have assembled := Tromino.completable_assemble localCompletion separate
  have region : {c | ∃ o : Selected, c ∈ stateTarget o.val (booleanOutside (fun _ => false) o.val)} =
      (StripCaps.coreBand .I (162*count))ᶜ := by
    ext c
    constructor
    · rintro ⟨o,hc⟩ inside
      obtain ⟨i,hl,hu,hi⟩ := (selected_states_core palette (fun _ => false) count hn (by simp) (by simp) c).mpr inside
      rw [boolean_state_target] at hc hi
      obtain ⟨chosen,_,unique⟩ := boolean_groups_partition palette (fun _ => false) c
      have eq := (unique o.val hc).trans (unique i hi).symm
      exact o.property (eq.symm ▸ ⟨hl,hu⟩)
    · intro outside
      obtain ⟨o,ho,_⟩ := boolean_groups_partition palette (fun _ => false) c
      have target : c ∈ stateTarget o (booleanOutside (fun _ => false) o) := by rwa [boolean_state_target]
      have notBand : ¬ InBand count o.location := by
        intro hb
        exact outside ((selected_states_core palette (fun _ => false) count hn (by simp) (by simp) c).mp
          ⟨o,hb.1,hb.2,target⟩)
      exact ⟨⟨o,notBand⟩,target⟩
  have prefill : {f | ∃ o : Selected, f ∈ atomPrescribed o.val.location o.val.entry} =
      exteriorPrescribed palette count := by
    ext f
    constructor
    · rintro ⟨o,hf⟩
      exact ⟨o.val,o.property,hf⟩
    · rintro ⟨o,hb,hf⟩
      exact ⟨⟨o,hb⟩,hf⟩
  simp only [Finset.mem_coe] at assembled
  rwa [region,prefill] at assembled

theorem band_exterior_prescribed (palette : Cell → Fin 24) (count : Int) :
    bandPrescribed palette count ∪ exteriorPrescribed palette count = globalPrescribed palette := by
  rw [← prescribed_union]
  ext f
  constructor
  · rintro (⟨o,_,hf⟩ | ⟨o,_,hf⟩) <;> exact ⟨o,hf⟩
  · rintro ⟨o,hf⟩
    by_cases hb : InBand count o.location
    · exact Or.inl ⟨o,hb,hf⟩
    · exact Or.inr ⟨o,hb,hf⟩

theorem plane_completion_of_core (palette : Cell → Fin 24) (count : Int) (hn : 0 < count)
    (blank : ∀ location, ¬ InBand count location → palette location = 0)
    (core : Tromino.I.Completable (StripCaps.coreBand .I (162*count)) (bandPrescribed palette count)) :
    Tromino.I.Completable Set.univ (globalPrescribed palette) := by
  have result := core.union (exterior_completion palette count hn blank) disjoint_compl_right
  simpa only [Set.union_compl_self,band_exterior_prescribed] using result

end LeanTrominoes.CompletionPattern.IBricks
