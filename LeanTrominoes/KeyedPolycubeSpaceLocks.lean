/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedPolycubeSpaceSlices
import LeanTrominoes.KeyedPolycubeSpaceOrientation
import LeanTrominoes.KeyedPolycubeSpaceSmall
import LeanTrominoes.SlabCapObstruction
import LeanTrominoes.KeyedComplementRightNeighbor

/-! # Exact side-lock forcing in unrestricted three-dimensional space -/

namespace LeanTrominoes.KeyedPeriodicComplement

private theorem disjoint_middle_slice (n : Nat) (holes : Polyomino)
    (p : VoxelPlacement Unit)
    (hd : Disjoint (spaceTile n holes) (p.cells (fun _ => spaceTile n holes)))
    (slice : Polyomino)
    (lift : ∀ c ∈ slice, (c,1) ∈ p.cells (fun _ => spaceTile n holes)) :
    Disjoint (tile n holes) slice := by
  apply Finset.disjoint_left.mpr
  intro c hc hs
  exact Finset.disjoint_left.mp hd
    ((mem_spaceTile n holes (c,1)).mpr (Or.inl ⟨hc,by omega⟩)) (lift c hs)

theorem space_candidate (n : Nat) (holes : Polyomino) (lock : Cell)
    (inside : lock ∈ square n) (expected : Placement Bool)
    (forcing : ∀ a : Placement Bool,
      lock ∈ a.cells (pairTiles PlusRefinement.bumpy (tile n holes)) →
      Disjoint (tile n holes) (a.cells (pairTiles PlusRefinement.bumpy (tile n holes))) →
      a = expected)
    (cap : ∀ a : Placement Unit, lock ∈ a.cells (fun _ => square n) →
      ¬ Disjoint (tile n holes) (a.cells (fun _ => square n)))
    (p : VoxelPlacement Unit) (horizontal : p.symmetry.axis = 0)
    (covers : (lock,1) ∈ p.cells (fun _ => spaceTile n holes))
    (hd : Disjoint (spaceTile n holes) (p.cells (fun _ => spaceTile n holes))) :
    p.toPlanar.tag true = expected ∧ p.offset.2 = if p.symmetry.flip then 2 else 0 := by
  rcases (space_horizontal_cells n holes p horizontal (lock,1)).mp covers with h | h
  · have disjoint := disjoint_middle_slice n holes p hd
      (p.toPlanar.cells (fun _ => tile n holes)) (fun c hc =>
        (space_horizontal_cells n holes p horizontal (c,1)).mpr (Or.inl ⟨hc,h.2⟩))
    have eq := forcing (p.toPlanar.tag true) h.1 disjoint
    exact ⟨eq,space_background_height n holes p horizontal lock inside h.1 h.2 hd⟩
  · have disjoint := disjoint_middle_slice n holes p hd
      (p.toPlanar.cells (fun _ => square n)) (fun c hc =>
        (space_horizontal_cells n holes p horizontal (c,1)).mpr (Or.inr ⟨hc,h.2⟩))
    exact False.elim (cap p.toPlanar h.1 disjoint)

theorem space_vertical_candidate {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (p : VoxelPlacement Unit)
    (covers : ((2,3),1) ∈ p.cells (fun _ => spaceTile n holes))
    (hd : Disjoint (spaceTile n holes) (p.cells (fun _ => spaceTile n holes))) :
    p.symmetry.axis = 0 ∧
      p.toPlanar.tag true = (⟨true,.identity,(0,-(n : Int))⟩ : Placement Bool) ∧
      p.offset.2 = if p.symmetry.flip then 2 else 0 := by
  have horizontal := SpaceLock.vertical_background_horizontal hn holes admissible p covers hd
  exact ⟨horizontal,space_candidate n holes (2,3) (by rw [mem_square]; omega) _
    (vertical_candidate hn period holes admissible)
    (square_cannot_fill_vertical_lock hn holes admissible) p horizontal covers hd⟩

theorem space_right_candidate {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes) (p : VoxelPlacement Unit)
    (covers : (((n : Int)-4,2),1) ∈ p.cells (fun _ => spaceTile n holes))
    (hd : Disjoint (spaceTile n holes) (p.cells (fun _ => spaceTile n holes))) :
    p.symmetry.axis = 0 ∧
      p.toPlanar.tag true = (⟨true,.identity,((n : Int),0)⟩ : Placement Bool) ∧
      p.offset.2 = if p.symmetry.flip then 2 else 0 := by
  have horizontal := SpaceLock.right_background_horizontal hn period holes admissible p covers hd
  exact ⟨horizontal,space_candidate n holes ((n : Int)-4,2) (by rw [mem_square]; omega) _
    (right_candidate hn period holes admissible)
    (square_cannot_fill_right_lock hn holes admissible) p horizontal covers hd⟩

end LeanTrominoes.KeyedPeriodicComplement
