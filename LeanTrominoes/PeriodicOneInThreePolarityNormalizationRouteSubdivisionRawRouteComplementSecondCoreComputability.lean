/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementSecondArgumentsComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteTranslatePolylineComputability

/-! # Source-side complement raw-route core computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

def complementSecondRawRouteFromPeriod {Input Variable : Type*}
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (input : (Input × ClauseMetadata Variable) ×
      (Nat × PeriodicLiteral Variable)) : List Cell :=
  let arguments := complementSecondRawRouteArguments
    (Variable := Variable) period routes input
  PeriodicOrthocrossing.translatePolyline arguments.1 arguments.2

theorem complementSecondRawRouteFromPeriod_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec (complementSecondRawRouteFromPeriod
      (Variable := Variable) period routes) := by
  have arguments : Primrec (complementSecondRawRouteArguments
      (Variable := Variable) period routes) :=
    complementSecondRawRouteArguments_primrec
      period routes periodPrimrec routesPrimrec
  exact (translatePolyline_primrec.comp
    (Primrec.fst.comp arguments) (Primrec.snd.comp arguments)).of_eq
      fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
