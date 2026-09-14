/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIMicroGroups

namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 1000000

/-- Translation of a microcell by an integer number of microcell spacings. -/
theorem micro_translation (delta i c : Cell) :
    Cell.add (microOrigin delta) c ∈ microRegion (Cell.add delta i) ↔ c ∈ microRegion i := by
  rw [mem_microRegion,mem_microRegion]
  have hx : (Cell.add (microOrigin delta) c).1 - 18 * (Cell.add delta i).1 =
      c.1 - 18 * i.1 := by dsimp [Cell.add,microOrigin]; omega
  have hy : (Cell.add (microOrigin delta) c).2 - 27 * (Cell.add delta i).2 =
      c.2 - 27 * i.2 := by dsimp [Cell.add,microOrigin]; omega
  rw [hx,hy]

theorem micro_image (delta i : Cell) :
    (microRegion i).image (Cell.add (microOrigin delta)) = microRegion (Cell.add delta i) := by
  ext c
  constructor
  · intro hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    exact (micro_translation delta i d).mpr hd
  · intro hc
    have cancel : Cell.add (microOrigin delta) (Cell.sub c (microOrigin delta)) = c := by
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    refine Finset.mem_image.mpr ⟨Cell.sub c (microOrigin delta),?_,cancel⟩
    apply (micro_translation delta i _).mp
    rwa [cancel]

theorem group_translation (delta : Cell) (s : Finset Cell) :
    groupRegion (s.image (Cell.add delta)) =
      (groupRegion s).image (Cell.add (microOrigin delta)) := by
  ext c
  constructor
  · intro hc
    obtain ⟨j,hj,hjc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    rw [← micro_image] at hjc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hjc
    exact Finset.mem_image.mpr ⟨d,Finset.mem_biUnion.mpr ⟨i,hi,hd⟩,rfl⟩
  · intro hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨i,hi,hid⟩ := Finset.mem_biUnion.mp hd
    exact Finset.mem_biUnion.mpr
      ⟨Cell.add delta i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,(micro_translation delta i d).mpr hid⟩

end LeanTrominoes.CompletionPattern.IBricks
