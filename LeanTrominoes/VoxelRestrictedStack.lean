/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeTranslation
import LeanTrominoes.VoxelTranslationTiling

/-! # Repeat an exact finite-height band tiling throughout space -/

namespace LeanTrominoes

theorem voxel_space_tileableWith_of_band {ι : Type*} (tiles : ι → Polycube)
    (placements : Set (VoxelPlacement ι))
    (band : IsVoxelTiling tiles {c | -1 ≤ c.2 ∧ c.2 ≤ 3} placements)
    (allowed : VoxelPlacement ι → Prop)
    (legal : ∀ p ∈ placements, allowed p)
    (stable : ∀ p k, allowed p → allowed (p.shift ((0,0),5*k))) :
    VoxelTileableWith tiles Set.univ allowed := by
  let stacked : Set (VoxelPlacement ι) :=
    {p | ∃ k : Int, ∃ q ∈ placements, p = q.shift ((0,0),5*k)}
  refine ⟨stacked,⟨?_,?_⟩,?_⟩
  · intro _ _ _ _
    trivial
  · intro c _
    let k : Int := (c.2+1)/5
    let bandCell : Voxel := (c.1,c.2-5*k)
    have height : -1 ≤ bandCell.2 ∧ bandCell.2 ≤ 3 := by dsimp [bandCell,k]; omega
    have translated : Voxel.add ((0,0),5*k) bandCell = c := by
      simp [bandCell,Voxel.add,Cell.add]
    obtain ⟨p,⟨hp,hc⟩,unique⟩ := band.uniqueCover bandCell height
    refine ⟨p.shift ((0,0),5*k),⟨⟨k,p,hp,rfl⟩,?_⟩,?_⟩
    · rw [← translated,VoxelPlacement.mem_shift_cells]
      exact hc
    · rintro _ ⟨⟨l,q,hq,rfl⟩,hqc⟩
      let other : Voxel := (c.1,c.2-5*l)
      have moved : Voxel.add ((0,0),5*l) other = c := by simp [other,Voxel.add,Cell.add]
      have source : other ∈ q.cells tiles := by
        apply (VoxelPlacement.mem_shift_cells tiles ((0,0),5*l) q other).mp
        rwa [moved]
      have bounds := band.tilesInside q hq other source
      have same : l = k := by change -1 ≤ other.2 ∧ other.2 ≤ 3 at bounds; dsimp [other,bandCell] at *; omega
      subst l
      exact congrArg (VoxelPlacement.shift ((0,0),5*k)) (unique q ⟨hq,source⟩)

  · rintro p ⟨k,q,hq,rfl⟩
    exact stable q k (legal q hq)

end LeanTrominoes
