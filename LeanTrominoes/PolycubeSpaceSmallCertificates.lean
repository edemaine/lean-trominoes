/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSpaceLockData

/-! # The fixed 45-cube tile cannot fill either side lock -/

namespace LeanTrominoes.SpaceLock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem small_at_vertical_lock : ∀ s : CubeSymmetry,
    ForcedOverlap Polycube.bumpyThree verticalOffsets s := by decide +kernel

theorem small_at_right_lock : ∀ s : CubeSymmetry,
    ForcedOverlap Polycube.bumpyThree rightOffsets s := by decide +kernel

end LeanTrominoes.SpaceLock
