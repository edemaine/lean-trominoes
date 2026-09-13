/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeTallSlabSlices

/-! # Unconditional planar recovery from arbitrary taller-slab tilings -/

namespace LeanTrominoes.KeyedPeriodicComplement

theorem planar_tileable_of_tall_slab {height n : Nat} (hh : 3 ≤ height)
    (wide : height < n) (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (tileable : VoxelTileable (tallSlabFamily height n holes) (voxelSlab height)) :
    Tileable (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ := by
  obtain ⟨ps,tiling,grid⟩ := tall_slab_tileable_has_grid hh wide hn period holes admissible tileable
  have slice := tall_slab_middle_slice hh wide hn period holes admissible ps tiling grid
  refine ⟨VoxelPlacement.toPlanar '' ps,?_,?_⟩
  · intro _ _ _ _
    trivial
  · intro c _
    obtain ⟨p,⟨hp,hc⟩,unique⟩ := tiling.uniqueCover (c,1) (by
      change 0 ≤ (1 : Int) ∧ (1 : Int) < height
      omega)
    refine ⟨p.toPlanar,⟨⟨p,hp,rfl⟩,(slice p hp c).mp hc⟩,?_⟩
    rintro _ ⟨⟨q,hq,rfl⟩,hqc⟩
    exact congrArg VoxelPlacement.toPlanar (unique q ⟨hq,(slice q hq c).mpr hqc⟩)

end LeanTrominoes.KeyedPeriodicComplement
