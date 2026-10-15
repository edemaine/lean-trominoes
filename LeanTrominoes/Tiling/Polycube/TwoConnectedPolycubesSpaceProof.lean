/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polycube.TwoConnectedPolycubesSpaceHardness
import LeanTrominoes.Tiling.Polycube.TwoConnectedPolycubesUpperBound
import LeanTrominoes.Tiling.Polycube.BumpyPolycubeConnected

/-! # Two connected polycubes: full space co-r.e. completeness -/

namespace LeanTrominoes.TwoConnectedPolycubes

theorem spaceProved : spaceStatement := ⟨space_coRE, space_coREHard⟩

end LeanTrominoes.TwoConnectedPolycubes
