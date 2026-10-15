/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polycube.TwoConnectedPolycubesSlabHardness
import LeanTrominoes.Tiling.Polycube.TwoConnectedPolycubesUpperBound
import LeanTrominoes.Tiling.Polycube.BumpyPolycubeConnected

/-! # Two connected polycubes: height-two slab co-r.e. completeness -/

namespace LeanTrominoes.TwoConnectedPolycubes

theorem slabTwoProved : slabTwoStatement := ⟨slabTwo_coRE, slabTwo_coREHard⟩

end LeanTrominoes.TwoConnectedPolycubes
