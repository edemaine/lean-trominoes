/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeSpaceLockData

/-! # Upright protruding keys overlap occupied side-lock witnesses -/

namespace LeanTrominoes.SpaceLock

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem vertical_key_at_vertical_lock : ∀ s : CubeSymmetry, s.axis ≠ 0 →
    ForcedOverlap (keyPrism KeyedPeriodicComplement.verticalLock) verticalOffsets s := by decide +kernel

theorem horizontal_key_at_vertical_lock : ∀ s : CubeSymmetry, s.axis ≠ 0 →
    ForcedOverlap (keyPrism horizontalKey) verticalOffsets s := by decide +kernel

theorem vertical_key_at_right_lock : ∀ s : CubeSymmetry, s.axis ≠ 0 →
    ForcedOverlap (keyPrism KeyedPeriodicComplement.verticalLock) rightOffsets s := by decide +kernel

theorem horizontal_key_at_right_lock : ∀ s : CubeSymmetry, s.axis ≠ 0 →
    ForcedOverlap (keyPrism horizontalKey) rightOffsets s := by decide +kernel

end LeanTrominoes.SpaceLock
