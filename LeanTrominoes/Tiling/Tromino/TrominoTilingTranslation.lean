/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.SeparatedTrominoRegions

/-! # Translating geometric tromino tilings -/
namespace LeanTrominoes.Tromino
open Gadget

def translatedRegion (offset : Cell) (region : Set Cell) : Set Cell :=
  {cell | ∃ base∈region, Cell.add offset base=cell}

theorem IsFootprintTiling.translateSeparated {t : Tromino} {region : Set Cell}
    {tiles : Set (Finset Cell)} (tiling : IsFootprintTiling t region tiles) (offset : Cell) :
    IsFootprintTiling t (translatedRegion offset region)
      {tile | ∃ base∈tiles, translateFootprint offset base=tile} := by
  constructor
  · rintro tile ⟨base,member,rfl⟩
    constructor
    · obtain ⟨p,hp⟩ := (tiling.tilesInside base member).1
      refine ⟨translatePlacement offset p,?_⟩
      rw [translatePlacement_cells,hp]
    · intro cell hc
      obtain ⟨old,ho,rfl⟩ := Finset.mem_image.mp hc
      exact ⟨old,(tiling.tilesInside base member).2 old ho,rfl⟩
  · rintro cell ⟨base,member,rfl⟩
    obtain ⟨tile,⟨ht,hc⟩,unique⟩ := tiling.uniqueCover base member
    refine ⟨translateFootprint offset tile,⟨⟨tile,ht,rfl⟩,?_⟩,?_⟩
    · exact (add_mem_translateFootprint_iff offset base tile).mpr hc
    · rintro other ⟨⟨old,ho,rfl⟩,covers⟩
      have same := unique old ⟨ho,(add_mem_translateFootprint_iff offset base old).mp covers⟩
      exact congrArg (translateFootprint offset) same

theorem tileable_translate {t : Tromino} {region : Set Cell}
    (tileable : t.Tileable region) (offset : Cell) : t.Tileable (translatedRegion offset region) := by
  obtain ⟨tiles,tiling⟩ := (t.tileable_iff_exists_footprintTiling _).mp tileable
  exact (t.tileable_iff_exists_footprintTiling _).mpr ⟨_,tiling.translateSeparated offset⟩

@[simp] theorem translatedRegion_zero (region : Set Cell) : translatedRegion (0,0) region=region := by
  ext cell
  simp [translatedRegion,Cell.add]

end LeanTrominoes.Tromino
