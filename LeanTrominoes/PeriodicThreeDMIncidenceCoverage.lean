/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMIncidenceTagElementOrder

/-! # Positive-degree elements have canonical incidence tags -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

theorem incidenceElement_surjective_of_degree_positive (p : PeriodicThreeDM)
    (color : WireColor) (atom : Nat) (positive : 0 < p.degree color atom) :
    ∃ tag ∈ p.incidenceTags, p.incidenceElement tag = (color,atom) := by
  have nonempty : ∃ incidence, incidence ∈ p.incidences color atom := by
    cases h : p.incidences color atom with
    | nil => simp [degree,h] at positive
    | cons i rest => exact ⟨i,by simp⟩
  obtain ⟨incidence,member⟩ := nonempty
  have filtered : (⟨incidence.tripleIndex,color⟩ : IncidenceTag) ∈
      p.incidenceTags.filter (fun tag => decide (p.incidenceElement tag = (color,atom))) := by
    rw [incidenceTags_filter_element]
    exact List.mem_map.mpr ⟨incidence,member,rfl⟩
  have h := List.mem_filter.mp filtered
  exact ⟨_,h.1,of_decide_eq_true h.2⟩

theorem incidenceElement_surjective_of_degreeTwoOrThree (p : PeriodicThreeDM)
    (degrees : p.DegreeTwoOrThree) (color : WireColor) (atom : Nat)
    (bound : atom < p.elementCount color) :
    ∃ tag ∈ p.incidenceTags, p.incidenceElement tag = (color,atom) := by
  apply incidenceElement_surjective_of_degree_positive
  have h := degrees color atom bound
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  omega

end LeanTrominoes.PeriodicThreeDM
