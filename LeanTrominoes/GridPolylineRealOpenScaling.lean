/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealAffineSimplicity

/-! # Nonzero integral scaling preserves open real simplicity -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem IsRealOpenSimple.scale {route : List Cell} (simple : IsRealOpenSimple route) {factor : Int} (nonzero : factor ≠ 0) :
    IsRealOpenSimple (scalePolyline factor route) := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  apply simple.map (Cell.scale factor) (Cell.scale_injective nonzero)
    (fun point => (point.1/(factor : ℝ),point.2/(factor : ℝ)))
  · intro segment point contains
    exact (GridSegment.realContains_scale_inverse segment nonzero point).mp contains
  · intro point cell equal
    have hx := congrArg Prod.fst equal
    have hy := congrArg Prod.snd equal
    apply Prod.ext
    · simpa [realCell,Cell.scale,mul_comm] using (div_eq_iff realNonzero).mp hx
    · simpa [realCell,Cell.scale,mul_comm] using (div_eq_iff realNonzero).mp hy

end LeanTrominoes.GridPolyline
