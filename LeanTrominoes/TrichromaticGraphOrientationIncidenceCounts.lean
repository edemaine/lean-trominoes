/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationIncidenceIndices
import Mathlib.Data.Finset.Card

/-! # Degrees and color counts as finite sets of incidence indices -/
namespace LeanTrominoes.TrichromaticGraphOrientation
open Gadget

def incidentIndices (input : Input) (vertex : Nat) : Finset Nat :=
  ((List.range (2*input.2.length)).filter fun index => (incidenceAt input index).1 = vertex).toFinset

def colorIndices (input : Input) (vertex : Nat) (color : WireColor) : Finset Nat :=
  ((List.range (2*input.2.length)).filter fun index =>
    (incidenceAt input index).1 = vertex ∧ (incidenceAt input index).2.2 = color).toFinset

theorem mem_incidentIndices (input : Input) (vertex index : Nat) :
    index ∈ incidentIndices input vertex ↔ index < 2*input.2.length ∧ (incidenceAt input index).1 = vertex := by
  simp [incidentIndices]

theorem mem_colorIndices (input : Input) (vertex index : Nat) (color : WireColor) :
    index ∈ colorIndices input vertex color ↔ index < 2*input.2.length ∧
      (incidenceAt input index).1 = vertex ∧ (incidenceAt input index).2.2 = color := by
  simp [colorIndices]

theorem degree_eq_card (input : Input) (vertex : Nat) :
    (colors input vertex).length = (incidentIndices input vertex).card := by
  rw [incidentIndices,List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  simp [colors,endsAt,ends_eq_incidenceIndices,List.filter_map,Function.comp_def]

theorem colorCount_eq_card (input : Input) (vertex : Nat) (color : WireColor) :
    (colors input vertex).count color = (colorIndices input vertex color).card := by
  rw [colorIndices,List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  have helper (indices : List Nat) :
      ((indices.filter fun index => (incidenceAt input index).1 = vertex).map
        fun index => (incidenceAt input index).2.2).count color =
      (indices.filter fun index => decide ((incidenceAt input index).1 = vertex ∧
        (incidenceAt input index).2.2 = color)).length := by
    induction indices with
    | nil => rfl
    | cons index indices ih =>
      by_cases owner : (incidenceAt input index).1 = vertex <;>
        by_cases same : (incidenceAt input index).2.2 = color <;>
        simpa [owner,same] using ih
  simpa [colors,endsAt,ends_eq_incidenceIndices,List.filter_map,List.map_map,Function.comp_def] using
    helper (List.range (2*input.2.length))

theorem degree_three_iff (input : Input) (vertex : Nat) : (colors input vertex).length = 3 ↔
    ∃ first < 2*input.2.length, ∃ second < 2*input.2.length, ∃ third < 2*input.2.length,
      first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      (incidenceAt input first).1 = vertex ∧ (incidenceAt input second).1 = vertex ∧
      (incidenceAt input third).1 = vertex ∧
      ∀ index < 2*input.2.length, (incidenceAt input index).1 = vertex →
        index = first ∨ index = second ∨ index = third := by
  rw [degree_eq_card,Finset.card_eq_three]
  constructor
  · rintro ⟨first,second,third,different,firstThird,secondThird,equal⟩
    have firstMember : first ∈ incidentIndices input vertex := by rw [equal]; simp
    have secondMember : second ∈ incidentIndices input vertex := by rw [equal]; simp
    have thirdMember : third ∈ incidentIndices input vertex := by rw [equal]; simp
    obtain ⟨firstBound,firstOwner⟩ := (mem_incidentIndices input vertex first).mp firstMember
    obtain ⟨secondBound,secondOwner⟩ := (mem_incidentIndices input vertex second).mp secondMember
    obtain ⟨thirdBound,thirdOwner⟩ := (mem_incidentIndices input vertex third).mp thirdMember
    refine ⟨first,firstBound,second,secondBound,third,thirdBound,different,firstThird,secondThird,
      firstOwner,secondOwner,thirdOwner,?_⟩
    intro index bound owner
    have member := (mem_incidentIndices input vertex index).mpr ⟨bound,owner⟩
    simpa only [equal,Finset.mem_insert,Finset.mem_singleton] using member
  · rintro ⟨first,firstBound,second,secondBound,third,thirdBound,different,firstThird,secondThird,
      firstOwner,secondOwner,thirdOwner,cover⟩
    refine ⟨first,second,third,different,firstThird,secondThird,?_⟩
    ext index
    rw [mem_incidentIndices]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨bound,owner⟩; exact cover index bound owner
    · rintro (rfl | rfl | rfl) <;> exact ⟨by assumption,by assumption⟩

theorem color_one_iff (input : Input) (vertex : Nat) (color : WireColor) :
    (colors input vertex).count color = 1 ↔
      ∃ first < 2*input.2.length, (incidenceAt input first).1 = vertex ∧
        (incidenceAt input first).2.2 = color ∧
        ∀ second < 2*input.2.length,
          (incidenceAt input second).1 = vertex → (incidenceAt input second).2.2 = color → second = first := by
  rw [colorCount_eq_card,Finset.card_eq_one]
  constructor
  · rintro ⟨first,equal⟩
    have member : first ∈ colorIndices input vertex color := by rw [equal]; simp
    obtain ⟨bound,owner,same⟩ := (mem_colorIndices input vertex first color).mp member
    refine ⟨first,bound,owner,same,?_⟩
    intro second secondBound secondOwner secondSame
    have member := (mem_colorIndices input vertex second color).mpr ⟨secondBound,secondOwner,secondSame⟩
    simpa only [equal,Finset.mem_singleton] using member
  · rintro ⟨first,bound,owner,same,unique⟩
    refine ⟨first,?_⟩
    ext second
    rw [mem_colorIndices,Finset.mem_singleton]
    constructor
    · rintro ⟨secondBound,secondOwner,secondSame⟩; exact unique second secondBound secondOwner secondSame
    · rintro rfl; exact ⟨bound,owner,same⟩

theorem monochromatic_iff (input : Input) (vertex : Nat) :
    (∃ color : WireColor, ∀ c ∈ colors input vertex, c = color) ↔
      ∃ color : WireColor, ∀ index < 2*input.2.length,
        (incidenceAt input index).1 = vertex → (incidenceAt input index).2.2 = color := by
  apply exists_congr; intro color
  simp only [colors,endsAt,ends_eq_incidenceIndices,List.mem_map,List.mem_filter,List.mem_range]
  constructor
  · intro h index bound owner
    apply h _
    exact ⟨_,⟨⟨index,bound,rfl⟩,by simpa using owner⟩,rfl⟩
  · intro h c member
    obtain ⟨incidence,⟨⟨index,bound,rfl⟩,owner⟩,rfl⟩ := member
    exact h index bound (by simpa using owner)

end LeanTrominoes.TrichromaticGraphOrientation
