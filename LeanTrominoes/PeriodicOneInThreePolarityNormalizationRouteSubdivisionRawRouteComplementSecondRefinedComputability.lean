/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRefinedComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementSecondSourceInputComputability

/-! # Source-side complement refined-route computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

def complementSecondRefinedRoute {Input Metadata Variable : Type*}
    (sourceClauseIndex : Metadata → Nat)
    (routes : Input → Nat → Nat → List Cell)
    (input : (Input × Metadata) ×
      (Nat × PeriodicLiteral Variable)) : List Cell :=
  let query := complementSecondSourceRouteInput sourceClauseIndex input
  refinedRoute (routes query.1.1) query.1.2 query.2

theorem complementSecondRefinedRoute_primrec
    {Input Metadata Variable : Type*}
    [Primcodable Input] [Primcodable Metadata] [Primcodable Variable]
    (sourceClauseIndex : Metadata → Nat)
    (routes : Input → Nat → Nat → List Cell)
    (sourceClauseIndexPrimrec : Primrec sourceClauseIndex)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec (complementSecondRefinedRoute
      (Variable := Variable) sourceClauseIndex routes) := by
  exact ((refinedRoute_primrec routes routesPrimrec).comp
    (complementSecondSourceRouteInput_primrec
      sourceClauseIndex sourceClauseIndexPrimrec)).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
