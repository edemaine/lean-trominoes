/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteBasicComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementComputability

/-! # Raw route computability for routed polarity normalization -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

/-- Selecting the raw route from one generated clause's origin metadata is
primitive recursive. -/
theorem rawRouteForMetadata_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (routes : Input → Nat → Nat → List Cell)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × ClauseMetadata Variable) × Nat =>
      rawRouteForMetadata
        ({ period := period input.1.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable)
        (routes input.1.1) input.1.2 input.2 := by
  let RouteInput := (Input × ClauseMetadata Variable) × Nat
  have origin : Primrec fun input : RouteInput =>
      ClauseOrigin.equivData input.1.2.origin :=
    (ClauseOrigin.equivData_primrec (Variable := Variable)).comp
      ((ClauseMetadata.origin_primrec (Variable := Variable)).comp
        (Primrec.snd.comp Primrec.fst))
  have normalized : Primrec₂ fun (input : RouteInput) (_unit : Unit) =>
      normalizedRawRoute (routes input.1.1) input.1.2 input.2 :=
    ((normalizedRawRoute_primrec routes routesPrimrec).comp
      Primrec.fst).to₂
  have complement : Primrec₂ fun (input : RouteInput)
      (data : Nat × PeriodicLiteral Variable) =>
      complementRawRoute
        ({ period := period input.1.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable)
        (routes input.1.1) input.1.2 data input.2 := by
    change Primrec fun combined : RouteInput ×
        (Nat × PeriodicLiteral Variable) =>
      complementRawRoute
        ({ period := period combined.1.1.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable)
        (routes combined.1.1.1) combined.1.1.2 combined.2
          combined.1.2
    exact (complementRawRoute_primrec period routes
      periodPrimrec routesPrimrec).comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            Primrec.snd)
          (Primrec.snd.comp Primrec.fst))
  exact (Primrec.sumCasesOn origin normalized complement).of_eq
    fun input => by
      unfold rawRouteForMetadata
      cases input.1.2.origin <;> rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
