/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedPlacementComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionPositionComputability

/-!
# Placement computability for routed polarity normalization

This module specializes the positioned placement interface to the two route
subdivision vertices and then applies the final fresh-variable gauge.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The ungauged routed placement period is primitive recursive. -/
theorem rawPlacement_period_primrec
    {Input Variable : Type*} [Primcodable Input]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period) :
    Primrec fun input =>
      (rawPlacement (sourcePlacement input) (routes input)).period := by
  have refinedPeriod : Primrec fun input =>
      (refinedPlacement (sourcePlacement input)).period :=
    (refinedPlacement_period_primrec
      (fun input => (sourcePlacement input).period) periodPrimrec).of_eq
        fun _ => rfl
  exact (_root_.LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositioned.placement_period_primrec
      (fun input => refinedPlacement (sourcePlacement input))
      refinedPeriod).of_eq fun _ => rfl

/-- Every ungauged routed variable position is primitive recursive from the
source placement and incidence-route queries. -/
theorem rawPlacement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (sourcePositionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : Input × PolarityNormalizedVariable Variable =>
      (rawPlacement
        (sourcePlacement input.1) (routes input.1)).position input.2 := by
  let refined := fun input => refinedPlacement (sourcePlacement input)
  let freshPosition := fun input (fresh : FreshOccurrence Variable) =>
    (rawPositions (sourcePlacement input) (routes input)).freshVariable fresh
  have refinedPosition : Primrec fun input : Input × Variable =>
      (refined input.1).position input.2 :=
    refinedPlacement_position_primrec
      (fun input => (sourcePlacement input).period)
      (fun input atom => (sourcePlacement input).position atom)
      sourcePositionPrimrec
  have freshPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        freshPosition input.1 input.2 :=
    rawPositions_freshVariable_primrec
      (fun input => (sourcePlacement input).period) routes
      periodPrimrec routesPrimrec
  exact (_root_.LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositioned.placement_position_primrec refined freshPosition
      refinedPosition freshPositionPrimrec).of_eq fun _ => rfl

/-- The final routed placement retains the primitive-recursive raw period. -/
theorem placement_period_primrec
    {Input Variable : Type*} [Primcodable Input]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period) :
    Primrec fun input =>
      (placement (sourcePlacement input) (routes input)).period :=
  (rawPlacement_period_primrec sourcePlacement routes periodPrimrec).of_eq
    fun _ => rfl

/-- The final fresh-variable gauge preserves pointwise primitive
recursiveness of every routed variable position. -/
theorem placement_position_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (sourcePositionPrimrec : Primrec fun input : Input × Variable =>
      (sourcePlacement input.1).position input.2)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : Input × PolarityNormalizedVariable Variable =>
      (placement
        (sourcePlacement input.1) (routes input.1)).position input.2 := by
  have rawPosition : Primrec fun input :
      Input × PolarityNormalizedVariable Variable =>
      (rawPlacement
        (sourcePlacement input.1) (routes input.1)).position input.2 :=
    rawPlacement_position_primrec sourcePlacement routes periodPrimrec
      sourcePositionPrimrec routesPrimrec
  have rawPeriod : Primrec fun input :
      Input × PolarityNormalizedVariable Variable =>
      (rawPlacement
        (sourcePlacement input.1) (routes input.1)).period :=
    (rawPlacement_period_primrec sourcePlacement routes periodPrimrec).comp
      Primrec.fst
  have gauge : Primrec fun input :
      Input × PolarityNormalizedVariable Variable =>
      freshGauge input.2 :=
    freshGauge_primrec.comp Primrec.snd
  have translatedGauge : Primrec fun input :
      Input × PolarityNormalizedVariable Variable =>
      (rawPlacement
        (sourcePlacement input.1) (routes input.1)).translation
          (freshGauge input.2) :=
    (Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp rawPeriod) gauge).of_eq
        fun _ => rfl
  exact (Computability.cell_sub_primrec.comp
    rawPosition translatedGauge).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
