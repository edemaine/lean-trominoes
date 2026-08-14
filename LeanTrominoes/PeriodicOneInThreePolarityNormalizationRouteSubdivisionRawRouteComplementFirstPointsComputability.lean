/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteBasicComputability

/-! # Clause-side complement subdivision-point computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

def complementFirstRawPoints {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata : ClauseMetadata Variable)
    (origin : Nat × PeriodicLiteral Variable) : List Cell :=
  [routePoint routes
      ((metadata.sourceClauseIndex, origin.1), origin.2) 2,
    routePoint routes
      ((metadata.sourceClauseIndex, origin.1), origin.2) 1]

theorem complementFirstRawPoints_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (routes : Input → Nat → Nat → List Cell)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input :
        (Input × ClauseMetadata Variable) ×
          (Nat × PeriodicLiteral Variable) =>
      complementFirstRawPoints
        (routes input.1.1) input.1.2 input.2 := by
  let RouteInput :=
    (Input × ClauseMetadata Variable) ×
      (Nat × PeriodicLiteral Variable)
  have clauseIndex : Primrec fun input : RouteInput =>
      input.1.2.sourceClauseIndex :=
    ClauseMetadata.sourceClauseIndex_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  have fresh : Primrec fun input : RouteInput =>
      (input.1.1,
        ((input.1.2.sourceClauseIndex, input.2.1), input.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (Primrec.pair clauseIndex (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  have pointTwo : Primrec fun input : RouteInput =>
      routePoint (routes input.1.1)
        ((input.1.2.sourceClauseIndex, input.2.1), input.2.2) 2 :=
    (routePoint_primrec routes routesPrimrec).comp
      (Primrec.pair fresh (Primrec.const 2))
  have pointOne : Primrec fun input : RouteInput =>
      routePoint (routes input.1.1)
        ((input.1.2.sourceClauseIndex, input.2.1), input.2.2) 1 :=
    (routePoint_primrec routes routesPrimrec).comp
      (Primrec.pair fresh (Primrec.const 1))
  exact (Primrec.list_cons.comp pointTwo
    (Primrec.list_cons.comp pointOne (Primrec.const []))).of_eq
      fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
