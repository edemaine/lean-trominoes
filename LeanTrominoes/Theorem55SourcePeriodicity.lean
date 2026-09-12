/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55SourcePreparation
import LeanTrominoes.PlusRefinementPeriodicity

/-! # Square periods of the prepared hard source -/

namespace LeanTrominoes

theorem PeriodicTrominoPadding.isSquarePeriodic (n : Nat) :
    IsSquarePeriodic n (region n) := by
  intro c i j
  simp [region, Cell.add, Int.add_emod]

namespace Theorem55Source

theorem isSquarePeriodic {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    IsSquarePeriodic (period presentation) (region presentation) := by
  apply IsSquarePeriodic.union
  · apply IsSquarePeriodic.recenter
    apply PeriodicRegion.isSquarePeriodic
    · simp only [Gadget.PeriodicOrthogonalDrawing.periodicRegion,
        Gadget.PeriodicOrthogonalDrawing.horizontalPeriod, presentation.normalizedOrthogonalDrawing_periods.1,
        period, Nat.cast_mul, Nat.cast_ofNat]
    · simp only [Gadget.PeriodicOrthogonalDrawing.periodicRegion,
        Gadget.PeriodicOrthogonalDrawing.verticalPeriod, presentation.normalizedOrthogonalDrawing_periods.2,
        period, Nat.cast_mul, Nat.cast_ofNat]
  · exact PeriodicTrominoPadding.isSquarePeriodic _

end Theorem55Source
end LeanTrominoes
