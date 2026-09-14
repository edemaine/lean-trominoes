/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTrominoCompletion

namespace LeanTrominoes

@[simp] theorem Cell.image_translate_cancel (v : Cell) (s : Finset Cell) :
    (s.image (Cell.add v)).image (Cell.add (Cell.sub (0,0) v)) = s := by
  simp [Finset.image_image,Function.comp_def,Cell.add,Cell.sub]

theorem Placement.shift_cells_image (p : Placement Unit) (t : Tromino) (v : Cell) :
    (p.shift v).cells (fun _ => t.cells) = (p.cells (fun _ => t.cells)).image (Cell.add v) := by
  simp [Placement.cells,Placement.shift,Finset.image_image,Function.comp_def,Cell.add,Int.add_assoc]

end LeanTrominoes

namespace LeanTrominoes.Tromino

/-- Translate a full footprint tiling and its region together. -/
theorem IsFootprintTiling.translate {t : Tromino} {region : Set Cell}
    {completed : Set (Finset Cell)} (h : t.IsFootprintTiling region completed) (v : Cell) :
    t.IsFootprintTiling (Cell.add v '' region)
      ((fun f => f.image (Cell.add v)) '' completed) := by
  classical
  constructor
  · rintro f ⟨g,hg,rfl⟩
    refine ⟨(h.tilesInside g hg).1.translate v,?_⟩
    intro c hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨d,(h.tilesInside g hg).2 d hd,rfl⟩
  · rintro c ⟨d,hd,rfl⟩
    obtain ⟨f,⟨hf,hfd⟩,unique⟩ := h.uniqueCover d hd
    refine ⟨f.image (Cell.add v),⟨⟨f,hf,rfl⟩,Finset.mem_image.mpr ⟨d,hfd,rfl⟩⟩,?_⟩
    rintro g ⟨⟨k,hk,rfl⟩,hkg⟩
    have hkd : d ∈ k := by
      obtain ⟨e,he,eq⟩ := Finset.mem_image.mp hkg
      exact (Cell.add_left_injective v eq) ▸ he
    rw [unique k ⟨hk,hkd⟩]

/-- Translation preserves completion, including the prescribed footprints. -/
theorem Completable.translate {t : Tromino} {region : Set Cell}
    {prescribed : Set (Finset Cell)} (h : t.Completable region prescribed) (v : Cell) :
    t.Completable (Cell.add v '' region)
      ((fun f => f.image (Cell.add v)) '' prescribed) := by
  obtain ⟨completed,h,retained⟩ := h
  exact ⟨_,h.translate v,Set.image_mono retained⟩

end LeanTrominoes.Tromino
