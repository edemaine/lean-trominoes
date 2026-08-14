/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementFirstComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementSecondComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementSelectorComputability

/-! # Complement raw-route computability for routed polarity normalization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

/-- The two translated halves of one split complement route. -/
def complementRawRoute {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata : ClauseMetadata Variable)
    (origin : Nat × PeriodicLiteral Variable)
    (literalIndex : Nat) : List Cell :=
  if literalIndex = 0 then
    complementFirstRawRoute sourcePlacement routes metadata origin
  else if literalIndex = 1 then
    complementSecondRawRoute sourcePlacement routes metadata origin
  else []

/-- Complement raw-route selection is primitive recursive. -/
theorem complementRawRoute_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        ((Input × ClauseMetadata Variable) ×
          (Nat × PeriodicLiteral Variable)) × Nat =>
      complementRawRoute
        ({ period := period input.1.1.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable)
        (routes input.1.1.1) input.1.1.2 input.1.2 input.2 := by
  let BranchInput :=
    (Input × ClauseMetadata Variable) ×
      (Nat × PeriodicLiteral Variable)
  let first : BranchInput → List Cell := fun input =>
    complementFirstRawRoute
      ({ period := period input.1.1
         position := fun _ : Variable => (0, 0) } :
        PeriodicVariablePlacement Variable)
      (routes input.1.1) input.1.2 input.2
  let second : BranchInput → List Cell := fun input =>
    complementSecondRawRoute
      ({ period := period input.1.1
         position := fun _ : Variable => (0, 0) } :
        PeriodicVariablePlacement Variable)
      (routes input.1.1) input.1.2 input.2
  have firstPrimrec : Primrec first :=
    complementFirstRawRoute_primrec period routes
      periodPrimrec routesPrimrec
  have secondPrimrec : Primrec second :=
    complementSecondRawRoute_primrec period routes
      periodPrimrec routesPrimrec
  exact (selectComplementRawRoute_primrec first second
    firstPrimrec secondPrimrec).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
