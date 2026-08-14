/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementSecondSuffixComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementShiftComputability

/-! # Source-side complement raw-route argument computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

def complementSecondRawRouteArguments {Input Variable : Type*}
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (input : (Input × ClauseMetadata Variable) ×
      (Nat × PeriodicLiteral Variable)) : Cell × List Cell :=
  (complementRawRouteShift (Variable := Variable) period input,
    complementSecondRawSuffix (routes input.1.1) input.1.2 input.2)

theorem complementSecondRawRouteArguments_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec (complementSecondRawRouteArguments
      (Variable := Variable) period routes) := by
  exact Primrec.pair
    (complementRawRouteShift_primrec period periodPrimrec)
    (complementSecondRawSuffix_primrec routes routesPrimrec)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
