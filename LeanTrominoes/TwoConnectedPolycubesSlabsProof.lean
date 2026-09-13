/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoConnectedPolycubesSlabsHardness
import LeanTrominoes.TwoConnectedPolycubesSlabProof
import LeanTrominoes.BumpyPolycubeTwoOrientation

/-! # Two connected polycubes: co-r.e. completeness at every fixed slab height greater than one -/

namespace LeanTrominoes.TwoConnectedPolycubes

theorem slabSmall_connected (height : Nat) : Polycube.IsConnected (slabSmall height) := by
  unfold slabSmall
  split_ifs
  · exact Polycube.bumpyOne_connected
  · exact Polycube.bumpyTwo_connected
  · exact Polycube.bumpyThree_connected

theorem slabSmall_card_le (height : Nat) : (slabSmall height).card ≤ 45 := by
  unfold slabSmall
  split_ifs <;> simp [Polycube.bumpyOne_card,Polycube.bumpyTwo_card,Polycube.bumpyThree_card]

/-- Every fixed height greater than one is co-r.e. complete, with at most
45 voxels in the fixed connected tile, allowing all cube symmetries. -/
theorem slabsProved : slabsStatement := by
  intro height hh
  by_cases two : height = 2
  · subst height
    simpa [slabProblem,slabSmall,slabTwoStatement,slabTwoProblem] using slabTwoProved
  · exact ⟨slab_coRE (slabSmall height) height,tall_slab_coREHard (by omega)⟩

end LeanTrominoes.TwoConnectedPolycubes
