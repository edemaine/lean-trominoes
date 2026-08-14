/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionPositionComputability
import LeanTrominoes.PositionedPeriodicCNFScalingComputability

/-!
# Formula computability for routed polarity normalization

This module composes clause-anchor normalization, geometric refinement,
route-selected complement positions, and the final fresh-variable gauge into
the exact positioned formula used by the routed construction.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The anchor-normalized and uniformly refined positioned source is
primitive recursive from the finite source and the placement period. -/
theorem refinedSource_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period) :
    Primrec fun input => refinedSource (source input) (placement input) := by
  have normalized : Primrec fun input =>
      (source input).anchorNormalize
        ({ period := (placement input).period
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable) :=
    PositionedPeriodicCNF.anchorNormalize_primrec source
      (fun input => (placement input).period) sourcePrimrec periodPrimrec
  exact ((PositionedPeriodicCNF.scale_primrec refinementFactor).comp
    normalized).of_eq fun _ => rfl

/-- The ungauged routed polarity-normalization formula is primitive
recursive from the finite source, placement period, and route query. -/
theorem rawFormula_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input =>
      rawFormula (source input) (placement input) (routes input) := by
  let refined := fun input =>
    refinedSource (source input) (placement input)
  let complementPosition := fun input (fresh : FreshOccurrence Variable) =>
    (rawPositions (placement input) (routes input)).complementClause fresh
  have refinedPrimrec : Primrec refined :=
    refinedSource_primrec source placement sourcePrimrec periodPrimrec
  have complementPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        complementPosition input.1 input.2 :=
    rawPositions_complementClause_primrec
      (fun input => (placement input).period) routes routesPrimrec
  exact
    (PeriodicOneInThreePolarityNormalizationPositioned.formula_primrec
      refined complementPosition refinedPrimrec
      complementPositionPrimrec).of_eq fun _ => rfl

/-- The final gauged positioned formula is primitive recursive from the
source presentation and its route query. -/
theorem formula_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input =>
      formula (source input) (placement input) (routes input) := by
  have raw : Primrec fun input =>
      rawFormula (source input) (placement input) (routes input) :=
    rawFormula_primrec source placement routes sourcePrimrec
      periodPrimrec routesPrimrec
  have gauge : Primrec fun input :
      Input × PolarityNormalizedVariable Variable =>
      freshGauge input.2 :=
    freshGauge_primrec.comp Primrec.snd
  exact PositionedPeriodicCNF.variableGauge_primrec
    (fun input =>
      rawFormula (source input) (placement input) (routes input))
    (fun _input => freshGauge) raw gauge

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
