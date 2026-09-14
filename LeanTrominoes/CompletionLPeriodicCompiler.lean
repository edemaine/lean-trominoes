/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLPeriodicPattern
import LeanTrominoes.CompletionLBrickEquivalence

/-! # Geometric correctness of the finite periodic L-prefill compiler -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.PeriodicPattern

set_option maxHeartbeats 2000000

theorem compile_prescribed (input : PeriodicPattern) :
    input.compile.prescribed .L = globalPrescribed input.palette := by
  ext f
  constructor
  · rintro ⟨q,hq,i,j,rfl⟩
    obtain ⟨site,hs,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    refine ⟨input.repeatSite site i j,p,?_,?_⟩
    · rwa [input.palette_repeat,input.palette_of_site hs]
    · rw [Placement.shift_cells_image,Placement.shift_cells_image,input.origin_repeat]
      simp only [Finset.image_image]
      apply Finset.image_congr
      intro c hc
      apply Prod.ext <;> dsimp [Function.comp_def,Cell.add] <;> omega
  · rintro ⟨location,p,hp,rfl⟩
    refine ⟨p.shift (origin (input.residue location)),List.mem_flatMap.mpr
      ⟨input.residue location,input.residue_mem_sites location,List.mem_map.mpr ⟨p,hp,rfl⟩⟩,
      location.1 / input.width,location.2 / input.height,?_⟩
    have eq := input.origin_repeat (input.residue location) (location.1 / input.width) (location.2 / input.height)
    rw [input.repeat_residue] at eq
    rw [Placement.shift_cells_image,Placement.shift_cells_image,eq]
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro c hc
    apply Prod.ext <;> dsimp [Function.comp_def,Cell.add] <;> omega

/-- The finite periodic prefill is completable exactly when its periodic
brick labels admit an arbitrary satisfying infinite Boolean network. -/
theorem compile_correct (input : PeriodicPattern) :
    PeriodicTrominoPrefill.planeProblem .L input.compile ↔
      ∃ external : Cell → Fin 4 → Bool, ExternalSeams external ∧
        ∀ location, Network (input.palette location) (external location) := by
  unfold PeriodicTrominoPrefill.planeProblem
  rw [input.compile_prescribed,completion_iff_brick_network]
  exact and_iff_right input.compile_full_rank

end LeanTrominoes.CompletionPattern.LBricks.PeriodicPattern
