/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedMetadataListComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedMetadataFreshIrrelevance
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionFormulaComputability

/-! # Routed polarity clause-metadata computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

/-- The complete routed source/origin metadata list is primitive recursive. -/
theorem clauseMetadata_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (placement : Input → PeriodicVariablePlacement Variable)
    (routes : Input → Nat → Nat → List Cell)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input => (placement input).period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input =>
      clauseMetadata (source input) (placement input) (routes input) := by
  let refined := fun input => refinedSource (source input) (placement input)
  let complementPosition := fun input (fresh : FreshOccurrence Variable) =>
    (rawPositions (placement input) (routes input)).complementClause fresh
  have refinedPrimrec : Primrec refined :=
    refinedSource_primrec source placement sourcePrimrec periodPrimrec
  have complementPositionPrimrec :
      Primrec fun input : Input × FreshOccurrence Variable =>
        complementPosition input.1 input.2 :=
    rawPositions_complementClause_primrec
      (fun input => (placement input).period) routes routesPrimrec
  exact (formulaClauseMetadata_primrec refined complementPosition
    refinedPrimrec complementPositionPrimrec).of_eq fun input =>
      formulaClauseMetadata_eq_of_complementClause
        { freshVariable := fun _ => (0, 0)
          complementClause := complementPosition input }
        (rawPositions (placement input) (routes input)) rfl
        (refined input)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
