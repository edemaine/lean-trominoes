/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionClauseMetadataComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawIncidenceRoutesLookupComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComputability

/-! # Raw routed-polarity incidence-route computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

/-- The complete ungauged split-route lookup is primitive recursive. -/
theorem rawIncidenceRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      rawIncidenceRoutes (source input.1.1) (placement input.1.1)
        (routes input.1.1) input.1.2 input.2 := by
  let metadata := fun input =>
    clauseMetadata (source input) (placement input) (routes input)
  let route := fun input (item : ClauseMetadata Variable) literalIndex =>
    rawRouteForMetadata (placement input) (routes input) item literalIndex
  have metadataPrimrec : Primrec metadata :=
    clauseMetadata_primrec source placement routes sourcePrimrec
      periodPrimrec routesPrimrec
  have routePrimrec : Primrec fun input :
      (Input × ClauseMetadata Variable) × Nat =>
      route input.1.1 input.1.2 input.2 :=
    rawRouteForMetadata_primrec
      (fun input => (placement input).period) routes
      periodPrimrec routesPrimrec
  exact (incidenceRouteFromMetadataList_primrec metadata route
    metadataPrimrec routePrimrec).of_eq fun input => by
      unfold incidenceRouteFromMetadataList rawIncidenceRoutes
      dsimp [metadata, route]
      cases (clauseMetadata (source input.1.1) (placement input.1.1)
        (routes input.1.1))[input.1.2]? <;> rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
