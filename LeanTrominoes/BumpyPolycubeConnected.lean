/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeConnectivity

/-! # The fixed slab and space tiles are connected -/

namespace LeanTrominoes.Polycube

private def predecessor (c : Voxel) : Voxel :=
  if c.2 ≠ 0 then (c.1, c.2 - 1)
  else if c.1.2 ≠ 0 then ((c.1.1, 0), 0)
  else if c.1.1 > 0 then ((c.1.1 - 1, 0), 0) else ((c.1.1 + 1, 0), 0)

private def rank (c : Voxel) : Nat := c.1.1.natAbs + c.1.2.natAbs + c.2.natAbs

theorem bumpyThree_connected : IsConnected bumpyThree := by
  apply connected_of_predecessor bumpyThree ((0, 0), 0) (by decide) predecessor rank
  decide +kernel

theorem bumpyOne_connected : IsConnected bumpyOne := by
  apply connected_of_predecessor bumpyOne ((0, 0), 0) (by decide) predecessor rank
  decide +kernel

end LeanTrominoes.Polycube
