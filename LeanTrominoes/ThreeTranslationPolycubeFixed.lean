/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubes

/-! # The two fixed connected polycubes have at most 45 voxels each -/

namespace LeanTrominoes.ThreeTranslationPolycubes

private def predecessor (vertical : Bool) (c : Voxel) : Voxel :=
  if c.2 ≠ 0 then (c.1, c.2 - 1)
  else if vertical then
    if c.1.1 ≠ 0 then ((0, c.1.2), 0)
    else if c.1.2 > 0 then ((0, c.1.2 - 1), 0) else ((0, c.1.2 + 1), 0)
  else if c.1.2 ≠ 0 then ((c.1.1, 0), 0)
  else if c.1.1 > 0 then ((c.1.1 - 1, 0), 0) else ((c.1.1 + 1, 0), 0)

private def rank (c : Voxel) : Nat := c.1.1.natAbs + c.1.2.natAbs + c.2.natAbs

theorem fixed_one_connected (vertical : Bool) : Polycube.IsConnected (fixed {0} vertical) := by
  cases vertical with
  | false =>
    apply Polycube.connected_of_predecessor _ ((0,0),0) (by decide) (predecessor false) rank
    decide +kernel
  | true =>
    apply Polycube.connected_of_predecessor _ ((0,0),0) (by decide) (predecessor true) rank
    decide +kernel

theorem fixed_two_connected (vertical : Bool) : Polycube.IsConnected (fixed {0,1} vertical) := by
  cases vertical with
  | false =>
    apply Polycube.connected_of_predecessor _ ((0,0),0) (by decide) (predecessor false) rank
    decide +kernel
  | true =>
    apply Polycube.connected_of_predecessor _ ((0,0),0) (by decide) (predecessor true) rank
    decide +kernel

theorem fixed_three_connected (vertical : Bool) : Polycube.IsConnected (fixed {0,1,2} vertical) := by
  cases vertical with
  | false =>
    apply Polycube.connected_of_predecessor _ ((0,0),0) (by decide) (predecessor false) rank
    decide +kernel
  | true =>
    apply Polycube.connected_of_predecessor _ ((0,0),0) (by decide) (predecessor true) rank
    decide +kernel

theorem fixed_card (layers : Finset Int) (vertical : Bool) : (fixed layers vertical).card = 15 * layers.card := by
  rw [fixed,Polycube.extrude_card]
  have planar : (ThreeTranslationPolyominoes.fixed vertical).card = 15 := by
    cases vertical <;> decide
  rw [planar]

theorem slab_fixed_connected (height : Nat) (vertical : Bool) :
    Polycube.IsConnected (fixed (slabLayers height) vertical) := by
  unfold slabLayers
  split_ifs
  · exact fixed_one_connected vertical
  · exact fixed_two_connected vertical
  · exact fixed_three_connected vertical

theorem slab_fixed_card_le (height : Nat) (vertical : Bool) :
    (fixed (slabLayers height) vertical).card ≤ 45 := by
  rw [fixed_card]
  unfold slabLayers
  split_ifs <;> decide

theorem slab_fixed_distinct (height : Nat) :
    fixed (slabLayers height) false ≠ fixed (slabLayers height) true := by
  unfold slabLayers
  split_ifs <;> decide

theorem space_fixed_distinct : fixed {0,1,2} false ≠ fixed {0,1,2} true := by decide

end LeanTrominoes.ThreeTranslationPolycubes
