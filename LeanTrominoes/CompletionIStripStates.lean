/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIStripCore

/-! # Completing a finite band of I-bricks from Boolean states -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

def InBand (count : Int) (location : Cell) : Prop := 0 ≤ location.2 ∧ location.2 < count

def bandPrescribed (palette : Cell → Fin 24) (count : Int) : Set (Finset Cell) :=
  {f | ∃ o : Occurrence palette, InBand count o.location ∧ f ∈ atomPrescribed o.location o.entry}

theorem band_completion_of_states (palette : Cell → Fin 24) (value : Cell → Bool)
    (count : Int) (hn : 0 < count)
    (top : ∀ x : Int, value (x,0) = false)
    (bottom : ∀ x : Int, value (x,6*count) = false)
    (realized : ∀ o : Occurrence palette, InBand count o.location →
      o.entry.1.pattern.Completable (booleanOutside value o)) :
    Tromino.I.Completable (StripCaps.coreBand .I (162*count)) (bandPrescribed palette count) := by
  let Selected := {o : Occurrence palette // InBand count o.location}
  have localCompletion (o : Selected) := state_completion o.val (booleanOutside value o.val) (realized o.val o.property)
  have separate (a b : Selected) (c : Cell)
      (ha : c ∈ stateTarget a.val (booleanOutside value a.val))
      (hb : c ∈ stateTarget b.val (booleanOutside value b.val)) : a = b := by
    rw [boolean_state_target] at ha hb
    obtain ⟨chosen,_,unique⟩ := boolean_groups_partition palette value c
    apply Subtype.ext
    exact (unique a.val ha).trans (unique b.val hb).symm
  have assembled := Tromino.completable_assemble localCompletion separate
  have region : {c | ∃ o : Selected, c ∈ stateTarget o.val (booleanOutside value o.val)} =
      StripCaps.coreBand .I (162*count) := by
    ext c
    rw [← selected_states_core palette value count hn top bottom]
    constructor
    · rintro ⟨o,hc⟩
      exact ⟨o.val,o.property.1,o.property.2,hc⟩
    · rintro ⟨o,hl,hu,hc⟩
      exact ⟨⟨o,hl,hu⟩,hc⟩
  have prefill : {f | ∃ o : Selected, f ∈ atomPrescribed o.val.location o.val.entry} =
      bandPrescribed palette count := by
    ext f
    constructor
    · rintro ⟨o,hf⟩
      exact ⟨o.val,o.property,hf⟩
    · rintro ⟨o,hb,hf⟩
      exact ⟨⟨o,hb⟩,hf⟩
  simp only [Finset.mem_coe] at assembled
  rwa [region,prefill] at assembled

theorem blank_state_realized (palette : Cell → Fin 24) (o : Occurrence palette)
    (blank : palette o.location = 0) :
    o.entry.1.pattern.Completable (booleanOutside (fun _ => false) o) := by
  rw [boolean_outside_local,Atom.boolean_completion_iff]
  have checked : ∀ e ∈ layout 0, e.1.BooleanRelation (fun _ => false) := by decide +kernel
  exact checked o.entry (by simpa [blank] using o.member)

end LeanTrominoes.CompletionPattern.IBricks
