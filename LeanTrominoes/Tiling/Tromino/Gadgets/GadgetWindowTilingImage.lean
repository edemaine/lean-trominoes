/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetAssembly

/-! # Replacing local placement records while preserving their footprints -/
namespace LeanTrominoes.Gadget

theorem IsWindowTiling.image_same_cells {t : Tromino} {window region : Finset Cell}
    {pattern : Finset (Placement Unit)} (valid : IsWindowTiling t window region pattern)
    (replace : Placement Unit → Placement Unit)
    (same : ∀ p, (replace p).cells (fun _ => t.cells) = p.cells (fun _ => t.cells)) :
    IsWindowTiling t window region (pattern.image replace) := by
  constructor
  · intro q member
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp member
    apply (mem_admissibleCandidates_iff t window region _).2
    simpa only [placementWindowCells,same] using
      (mem_admissibleCandidates_iff t window region p).1 (valid.1 hp)
  · intro c hc
    obtain ⟨p,⟨hp,hpc⟩,unique⟩ := valid.uniqueCover hc
    apply Finset.card_eq_one.mpr
    refine ⟨replace p,Finset.ext ?_⟩
    intro q
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨member,cover⟩
      obtain ⟨other,ho,rfl⟩ := Finset.mem_image.mp member
      rw [same] at cover
      exact congrArg replace (unique other ⟨ho,cover⟩)
    · intro equal
      subst q
      exact ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,by rwa [same]⟩

theorem portConfiguration_image_same_cells (t : Tromino) (gadget : Gadget)
    (pattern : Finset (Placement Unit)) (replace : Placement Unit → Placement Unit)
    (same : ∀ p, (replace p).cells (fun _ => t.cells) = p.cells (fun _ => t.cells)) :
    portConfiguration t gadget (pattern.image replace) = portConfiguration t gadget pattern := by
  rw [portConfiguration_eq_footprintPortConfiguration,portConfiguration_eq_footprintPortConfiguration]
  have footprints : windowFootprints t (pattern.image replace) = windowFootprints t pattern := by
    simp only [windowFootprints,Finset.image_image,Function.comp_def,same]
  rw [footprints]

end LeanTrominoes.Gadget
