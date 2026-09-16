/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBrickCompleteness
import LeanTrominoes.CompletionStripCapBands

/-! # The exact core occupied by a finite band of L-bricks -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

theorem group_row_bounds (palette : Cell → Fin 24) (o : Occurrence palette) (c : Cell)
    (hc : c ∈ groupAt o.location o.entry) :
    6*o.location.2 ≤ c.2 ∧ c.2 < 6*o.location.2+6 := by
  obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hc
  have bound := local_groups_inside (palette o.location) o.entry o.member hd
  simp only [brickMicroCells,Finset.mem_product,Finset.mem_Ico] at bound
  have y := congrArg Prod.snd eq
  simp only [Cell.add,brickMicroOrigin] at y
  omega

theorem selected_states_iff (palette : Cell → Fin 24) (value : Cell → Bool)
    (count : Int) (c : Cell) :
    (∃ o : Occurrence palette, 0 ≤ o.location.2 ∧ o.location.2 < count ∧
      c ∈ stateTarget o (booleanOutside value o)) ↔
      0 ≤ (booleanMicroOwner value c).2 ∧ (booleanMicroOwner value c).2 < 6*count := by
  constructor
  · rintro ⟨o,hl,hu,hc⟩
    rw [boolean_state_target] at hc
    have owned := (Finset.mem_filter.mp hc).2
    have bounds := group_row_bounds palette o _ owned
    omega
  · intro hc
    obtain ⟨o,ho,_⟩ := boolean_groups_partition palette value c
    have owned := (Finset.mem_filter.mp ho).2
    have bounds := group_row_bounds palette o _ owned
    refine ⟨o,by omega,by omega,?_⟩
    rwa [boolean_state_target]

theorem owner_row_core_band (value : Cell → Bool) (count : Int) (hn : 0 < count)
    (top : ∀ x : Int, value (x,0) = false)
    (bottom : ∀ x : Int, value (x,6*count) = false) (c : Cell) :
    (0 ≤ (booleanMicroOwner value c).2 ∧ (booleanMicroOwner value c).2 < 6*count) ↔
      c ∈ StripCaps.coreBand .L (36*count) := by
  by_cases atTop : c.2 = 0
  · simp [booleanMicroOwner,StripCaps.coreBand,StripCaps.width,atTop,top,aboveMicro]
    split_ifs <;> omega
  · by_cases atBottom : c.2 = 36*count
    · have row : c.2/6 = 6*count := by omega
      have rem : c.2%6 = 0 := by omega
      simp only [atBottom] at row rem
      simp only [booleanMicroOwner,atBottom,row,rem,bottom,aboveMicro,StripCaps.coreBand,StripCaps.width,Set.mem_setOf_eq]
      simp only [Bool.false_eq_true,if_false,if_true,Int.zero_emod,Int.zero_ediv,Int.zero_add]
      split_ifs <;> simp_all <;> omega
    · simp only [booleanMicroOwner,StripCaps.coreBand,Set.mem_setOf_eq,StripCaps.width]
      split_ifs <;> simp only [aboveMicro] <;> omega

theorem selected_states_core (palette : Cell → Fin 24) (value : Cell → Bool)
    (count : Int) (hn : 0 < count)
    (top : ∀ x : Int, value (x,0) = false)
    (bottom : ∀ x : Int, value (x,6*count) = false) (c : Cell) :
    (∃ o : Occurrence palette, 0 ≤ o.location.2 ∧ o.location.2 < count ∧
      c ∈ stateTarget o (booleanOutside value o)) ↔ c ∈ StripCaps.coreBand .L (36*count) :=
  (selected_states_iff palette value count c).trans (owner_row_core_band value count hn top bottom c)

end LeanTrominoes.CompletionPattern.LBricks
