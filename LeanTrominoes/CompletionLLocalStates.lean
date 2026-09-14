/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLLocalRestriction
import LeanTrominoes.TrominoCompletionTranslation

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

theorem atom_prescribed_recenter (location : Cell) (entry : Atom × Cell) :
    (fun f => f.image (Cell.add (Cell.sub (0,0) (atomOffset location entry)))) ''
      atomPrescribed location entry =
      (Tromino.L.finiteFootprints entry.1.pattern.prefill : Set (Finset Cell)) := by
  ext f
  constructor
  · rintro ⟨g,⟨p,hp,rfl⟩,rfl⟩
    simp only [Placement.shift_cells_image,Cell.image_translate_cancel]
    exact Finset.mem_image.mpr ⟨p,(entry.1.prefill_mem p).mpr hp,rfl⟩
  · intro hf
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hf
    refine ⟨(p.shift (atomOffset location entry)).cells (fun _ => Tromino.L.cells),
      ⟨p,(entry.1.prefill_mem p).mp hp,rfl⟩,?_⟩
    simp only [Placement.shift_cells_image,Cell.image_translate_cancel]

/-- The local states extracted from any plane completion satisfy the
canonical ASCII pattern, so the checked gadget truth tables apply. -/
theorem local_state_of_global (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    (global : Tromino.L.Completable Set.univ (globalPrescribed palette)) :
    ∃ outside : Finset Cell, outside ⊆ entry.1.boundary ∧ entry.1.pattern.Completable outside := by
  obtain ⟨outside,subset,completed⟩ := local_completion_of_global palette location he global
  let v := atomOffset location entry
  let inv := Cell.add (Cell.sub (0,0) v)
  have translated := completed.translate (Cell.sub (0,0) v)
  have regionEq : inv '' (↑(entry.1.pattern.region.image (Cell.add v) \ outside) : Set Cell) =
      (↑(entry.1.pattern.region \ outside.image inv) : Set Cell) := by
    rw [← Finset.coe_image,Finset.image_sdiff _ _ (Cell.add_left_injective _)]
    dsimp [inv]
    rw [Cell.image_translate_cancel]
  change Tromino.L.Completable
    (inv '' (↑(entry.1.pattern.region.image (Cell.add v) \ outside) : Set Cell))
    ((fun f => f.image inv) '' atomPrescribed location entry) at translated
  rw [regionEq] at translated
  have prescribedEq := atom_prescribed_recenter location entry
  change ((fun f => f.image inv) '' atomPrescribed location entry) = _ at prescribedEq
  rw [prescribedEq] at translated
  refine ⟨outside.image inv,?_,?_⟩
  · have bound := Finset.image_subset_image subset (f := inv)
    dsimp [inv,v] at bound
    rwa [Cell.image_translate_cancel] at bound
  · unfold Pattern.Completable Pattern.target
    rw [Atom.kind_eq]
    exact translated

end LeanTrominoes.CompletionPattern.LBricks
