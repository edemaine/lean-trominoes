/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementSecondRefinedComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedMetadataComputability

/-! # Source-side complement raw-route suffix computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

def complementSecondRawSuffix {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata : ClauseMetadata Variable)
    (origin : Nat × PeriodicLiteral Variable) : List Cell :=
  (refinedRoute routes metadata.sourceClauseIndex origin.1).drop 2

theorem complementSecondRawSuffix_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → Nat → Nat → List Cell)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × ClauseMetadata Variable) ×
          (Nat × PeriodicLiteral Variable) =>
      complementSecondRawSuffix
        (routes input.1.1) input.1.2 input.2 := by
  exact (Primrec.list_drop.comp (Primrec.const 2)
    (complementSecondRefinedRoute_primrec
      (ClauseMetadata.sourceClauseIndex : ClauseMetadata Variable → Nat)
      routes ClauseMetadata.sourceClauseIndex_primrec routesPrimrec)).of_eq
      fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
