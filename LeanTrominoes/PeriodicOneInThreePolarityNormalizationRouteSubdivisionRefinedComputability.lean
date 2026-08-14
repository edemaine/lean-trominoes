/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionScaleComputability
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

/-! # Refined routed-polarity polyline computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Refinement and unit subdivision preserve primitive recursiveness of a
source route query. -/
theorem refinedRoute_primrec
    {Input : Type*} [Primcodable Input]
    (routes : Input → Nat → Nat → List Cell)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      refinedRoute (routes input.1.1) input.1.2 input.2 := by
  have scaled : Primrec fun input : (Input × Nat) × Nat =>
      scalePolyline refinementFactor
        (routes input.1.1 input.1.2 input.2) :=
    scalePolyline_primrec.comp
      (Primrec.const (refinementFactor : Int)) routesPrimrec
  exact
    PeriodicThreeDM.NormalizationCompiler.unitSubdividePolyline_primrec.comp
      scaled

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
