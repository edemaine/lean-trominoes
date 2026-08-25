/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicIntegerPeriodQuotient
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNormalizationData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCoordinateBounds
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineAlgebraSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRoutePointGaugeData

/-! # Quotient semantics of affine route-point gauges -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Drawing-period quotient of a drawing-grid point. -/
def drawingPointGaugeAtPeriod (period : Nat) (point : Cell) : Cell :=
  (point.1 / period, point.2 / period)

theorem RouteDescriptor.gridSize_positive (descriptor : RouteDescriptor) :
    0 < descriptor.gridSize := by
  simp [RouteDescriptor.gridSize]

theorem RouteDescriptor.coordinate_add_gridSize_mul_ediv_eq_shift
    (descriptor : RouteDescriptor) {coordinate : Int}
    (bounds : descriptor.CoordinateInPeriod coordinate) (shift : Int) :
    (coordinate + descriptor.gridSize * shift) / descriptor.gridSize =
      shift := by
  exact coordinate_add_period_mul_ediv_eq_shift
    descriptor.gridSize_positive (le_of_lt bounds.1) bounds.2 shift

theorem RouteDescriptor.coordinate_ediv_gridSize_eq_zero
    (descriptor : RouteDescriptor) {coordinate : Int}
    (bounds : descriptor.CoordinateInPeriod coordinate) :
    coordinate / descriptor.gridSize = 0 := by
  simpa using descriptor.coordinate_add_gridSize_mul_ediv_eq_shift
    bounds 0

theorem RouteDescriptor.coordinate_add_gridSize_ediv_eq_one
    (descriptor : RouteDescriptor) {coordinate : Int}
    (bounds : descriptor.CoordinateInPeriod coordinate) :
    (coordinate + descriptor.gridSize) / descriptor.gridSize = 1 := by
  simpa using descriptor.coordinate_add_gridSize_mul_ediv_eq_shift
    bounds 1

theorem RouteDescriptor.coordinate_sub_gridSize_ediv_eq_neg_one
    (descriptor : RouteDescriptor) {coordinate : Int}
    (bounds : descriptor.CoordinateInPeriod coordinate) :
    (coordinate - descriptor.gridSize) / descriptor.gridSize = -1 := by
  simpa [sub_eq_add_neg] using
    descriptor.coordinate_add_gridSize_mul_ediv_eq_shift bounds (-1)

theorem RouteDescriptor.smallNonnegative_ediv_gridSize_eq_zero
    (descriptor : RouteDescriptor) {coordinate : Int}
    (nonnegative : 0 ≤ coordinate) (small : coordinate < 16) :
    coordinate / descriptor.gridSize = 0 := by
  apply Int.ediv_eq_zero_of_lt nonnegative
  have periodAtLeast : 16 ≤ descriptor.gridSize := by
    simp only [RouteDescriptor.gridSize]
    omega
  exact lt_of_lt_of_le small (by exact_mod_cast periodAtLeast)

/-- A strictly interior macrocell coordinate does not change the quotient by
a positive whole-macrocell period. -/
theorem macrocellCoordinate_ediv_scaledPeriod_eq_center_ediv
    {period : Nat} (periodPositive : 0 < period)
    {center localCoordinate : Int}
    (localNonnegative : 0 ≤ localCoordinate)
    (localSmall : localCoordinate < planarMacroScale) :
    (planarMacroScale * center + localCoordinate) /
        (planarMacroScale * period) = center / period := by
  have periodPositiveInt : (0 : Int) < period := by exact_mod_cast periodPositive
  have periodNe : (period : Int) ≠ 0 := ne_of_gt periodPositiveInt
  have scaledPeriodPositive :
      (0 : Int) < planarMacroScale * period :=
    mul_pos (by norm_num [planarMacroScale]) periodPositiveInt
  have scaledPeriodNe :
      (planarMacroScale * (period : Int)) ≠ 0 :=
    ne_of_gt scaledPeriodPositive
  have remainderNonnegative : 0 ≤ center % (period : Int) :=
    Int.emod_nonneg center periodNe
  have remainderSmall : center % (period : Int) < period :=
    Int.emod_lt_of_pos center periodPositiveInt
  have baseQuotient :
      (planarMacroScale * (center % (period : Int)) + localCoordinate) /
          (planarMacroScale * period) = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · nlinarith [show (0 : Int) < planarMacroScale by
        norm_num [planarMacroScale]]
    · nlinarith [show (0 : Int) < planarMacroScale by
        norm_num [planarMacroScale]]
  have centerDivision := Int.emod_add_mul_ediv center (period : Int)
  calc
    (planarMacroScale * center + localCoordinate) /
          (planarMacroScale * period) =
        ((planarMacroScale * (center % (period : Int)) + localCoordinate) +
          (center / (period : Int)) *
            (planarMacroScale * period)) /
          (planarMacroScale * period) := by
            congr 1
            nlinarith
    _ =
        (planarMacroScale * (center % (period : Int)) + localCoordinate) /
            (planarMacroScale * period) + center / (period : Int) := by
          rw [Int.add_mul_ediv_right _ _ scaledPeriodNe]
    _ = center / period := by rw [baseQuotient, zero_add]

/-- Adding any strictly interior macrocell coordinate to a refined drawing
point preserves its drawing-period gauge. -/
theorem carrierPositionGaugeAtPeriod_scale_add_local
    {period : Nat} (periodPositive : 0 < period)
    (point localPosition : Cell)
    (localBounds :
      0 ≤ localPosition.1 ∧
        localPosition.1 < planarMacroScale ∧
        0 ≤ localPosition.2 ∧
        localPosition.2 < planarMacroScale) :
    carrierPositionGaugeAtPeriod period
        (Cell.add (Cell.scale planarMacroScale point) localPosition) =
      drawingPointGaugeAtPeriod period point := by
  apply Prod.ext
  · exact macrocellCoordinate_ediv_scaledPeriod_eq_center_ediv
      periodPositive localBounds.1 localBounds.2.1
  · exact macrocellCoordinate_ediv_scaledPeriod_eq_center_ediv
      periodPositive localBounds.2.2.1 localBounds.2.2.2

namespace RouteDescriptorPairAffine

@[simp] theorem point_horizontal
    (horizontal vertical : Expression) :
    (point horizontal vertical).horizontal = horizontal := rfl

@[simp] theorem point_vertical
    (horizontal vertical : Expression) :
    (point horizontal vertical).vertical = vertical := rfl

@[simp] theorem evalPair_constant
    (value : Int) (pair : RouteDescriptor × RouteDescriptor) :
    (constant value).evalPair pair = value := by
  simp [constant, Expression.evalPair, Expression.eval]

/-- An affine point evaluates to the claimed drawing-period gauge on the
first member of a descriptor pair. -/
def Point.HasPeriodGauge
    (pair : RouteDescriptor × RouteDescriptor)
    (affinePoint : Point) (gauge : Cell) : Prop :=
  drawingPointGaugeAtPeriod pair.1.gridSize
    (affinePoint.evalPair pair) = gauge

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
