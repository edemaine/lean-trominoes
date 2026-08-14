/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementFirstCoreComputability

/-! # Clause-side complement raw-route computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

def complementFirstRawRoute {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata : ClauseMetadata Variable)
    (origin : Nat × PeriodicLiteral Variable) : List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (complementCanonicalShift sourcePlacement origin.2)
    (complementFirstRawPoints routes metadata origin)

theorem complementFirstRawRoute_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × ClauseMetadata Variable) ×
          (Nat × PeriodicLiteral Variable) =>
      complementFirstRawRoute
        ({ period := period input.1.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable)
        (routes input.1.1) input.1.2 input.2 := by
  exact (complementFirstRawRouteFromPeriod_primrec period routes
    periodPrimrec routesPrimrec).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
