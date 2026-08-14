/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionFormulaComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionPlacementComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawIncidenceRoutesComputability
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeCanonicalIncidenceRoutesComputability

/-! # Final routed-polarity incidence-route computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The complete final gauged incidence-route lookup is primitive recursive. -/
theorem incidenceRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      incidenceRoutes (source input.1.1) (placement input.1.1)
        (routes input.1.1) input.1.2 input.2 := by
  let rawSource := fun input =>
    rawFormula (source input) (placement input) (routes input)
  let rawSourcePlacement := fun input =>
    rawPlacement (placement input) (routes input)
  let rawRoutes := fun input =>
    rawIncidenceRoutes (source input) (placement input) (routes input)
  have rawSourcePrimrec : Primrec rawSource :=
    rawFormula_primrec source placement routes sourcePrimrec
      periodPrimrec routesPrimrec
  have rawPeriodPrimrec : Primrec fun input =>
      (rawSourcePlacement input).period :=
    rawPlacement_period_primrec placement routes periodPrimrec
  have gaugePrimrec : Primrec fun input :
      Input × PolarityNormalizedVariable Variable =>
      freshGauge input.2 :=
    freshGauge_primrec.comp Primrec.snd
  have rawRoutesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      rawRoutes input.1.1 input.1.2 input.2 :=
    rawIncidenceRoutes_primrec source placement routes sourcePrimrec
      periodPrimrec routesPrimrec
  exact (PositionedPeriodicCNF.variableGaugeCanonicalIncidenceRoutes_primrec
    rawSource rawSourcePlacement (fun _input => freshGauge) rawRoutes
    rawSourcePrimrec rawPeriodPrimrec gaugePrimrec rawRoutesPrimrec).of_eq
      fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
