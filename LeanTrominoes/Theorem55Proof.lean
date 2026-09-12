/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55Hardness
import LeanTrominoes.Theorem55UpperBound

/-! # Theorem 5.5: the plane result -/

namespace LeanTrominoes.Theorem55

/-- Plane tiling by the fixed connected 15-omino and an input disconnected
polyomino is co-r.e.-complete, allowing rotations and reflections. -/
theorem planeProved : planeStatement := ⟨coRE, coREHard⟩

end LeanTrominoes.Theorem55
