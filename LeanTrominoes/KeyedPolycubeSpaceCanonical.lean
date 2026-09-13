/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceSlices
import LeanTrominoes.PolycubePair
import LeanTrominoes.PolycubeTilingImage

/-! # Canonical records for vertically symmetric horizontal background tiles -/

namespace LeanTrominoes.KeyedPeriodicComplement

def spaceFamily (n : Nat) (holes : Polyomino) : Bool → Polycube :=
  Polycube.pairTiles Polycube.bumpyThree (spaceTile n holes)

def canonicalSpacePlacement (p : VoxelPlacement Bool) : VoxelPlacement Bool :=
  if p.kind = true ∧ p.symmetry.axis = 0 ∧ p.symmetry.flip = true then
    ⟨p.kind,⟨p.symmetry.planar,false,0⟩,(p.offset.1,p.offset.2-2)⟩
  else p

theorem canonicalSpacePlacement_unflipped (p : VoxelPlacement Bool)
    (kind : p.kind = true) (horizontal : p.symmetry.axis = 0) :
    (canonicalSpacePlacement p).symmetry.flip = false := by
  cases hf : p.symmetry.flip <;> simp [canonicalSpacePlacement,kind,horizontal,hf]

theorem canonicalSpacePlacement_cells (n : Nat) (holes : Polyomino)
    (p : VoxelPlacement Bool) :
    (canonicalSpacePlacement p).cells (spaceFamily n holes) = p.cells (spaceFamily n holes) := by
  unfold canonicalSpacePlacement
  split
  next h =>
    obtain ⟨kind,horizontal,flipped⟩ := h
    let q : VoxelPlacement Unit := ⟨(),⟨p.symmetry.planar,false,0⟩,(p.offset.1,p.offset.2-2)⟩
    have left : (⟨p.kind,⟨p.symmetry.planar,false,0⟩,(p.offset.1,p.offset.2-2)⟩ :
        VoxelPlacement Bool).cells (spaceFamily n holes) = q.cells (fun _ => spaceTile n holes) := by
      simp [q,VoxelPlacement.cells,spaceFamily,Polycube.pairTiles,kind]
    have right : p.cells (spaceFamily n holes) = p.untag.cells (fun _ => spaceTile n holes) := by
      simp [VoxelPlacement.cells,VoxelPlacement.untag,spaceFamily,Polycube.pairTiles,kind]
    rw [left,right]
    ext c
    rw [space_horizontal_cells n holes q rfl,
      space_horizontal_cells n holes p.untag horizontal]
    have planar : q.toPlanar = p.untag.toPlanar := rfl
    rw [planar]
    simp only [sourceHeight,q,VoxelPlacement.untag,flipped,Bool.false_eq_true,ite_false,ite_true]
    constructor <;> rintro (h | h)
    · exact Or.inl ⟨h.1,by omega⟩
    · exact Or.inr ⟨h.1,by omega⟩
    · exact Or.inl ⟨h.1,by omega⟩
    · exact Or.inr ⟨h.1,by omega⟩
  next h => rfl

theorem space_tiling_canonical {n : Nat} {holes : Polyomino}
    {placements : Set (VoxelPlacement Bool)}
    (tiling : IsVoxelTiling (spaceFamily n holes) Set.univ placements) :
    IsVoxelTiling (spaceFamily n holes) Set.univ (canonicalSpacePlacement '' placements) :=
  tiling.image canonicalSpacePlacement (canonicalSpacePlacement_cells n holes)

theorem space_canonical_unflipped {placements : Set (VoxelPlacement Bool)}
    {p : VoxelPlacement Bool} (hp : p ∈ canonicalSpacePlacement '' placements)
    (kind : p.kind = true) (horizontal : p.symmetry.axis = 0) : p.symmetry.flip = false := by
  obtain ⟨q,hq,rfl⟩ := hp
  by_cases h : q.kind = true ∧ q.symmetry.axis = 0 ∧ q.symmetry.flip = true
  · simp [canonicalSpacePlacement,h]
  · simp only [canonicalSpacePlacement,if_neg h] at *
    cases hf : q.symmetry.flip
    · rfl
    · exact False.elim (h ⟨kind,horizontal,hf⟩)

end LeanTrominoes.KeyedPeriodicComplement
