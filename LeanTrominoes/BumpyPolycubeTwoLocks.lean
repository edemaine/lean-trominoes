/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyPolycubeTwoCertificates
import LeanTrominoes.PolycubeSpaceLockData

/-! # The thickness-two tile obeys the same side-lock obstruction certificates -/

namespace LeanTrominoes.SpaceLock
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem small_two_at_vertical_lock : ∀ s : CubeSymmetry,
    ForcedOverlap Polycube.bumpyTwo verticalOffsets s := by decide +kernel

theorem small_two_at_right_lock : ∀ s : CubeSymmetry,
    ForcedOverlap Polycube.bumpyTwo rightOffsets s := by decide +kernel

end LeanTrominoes.SpaceLock
