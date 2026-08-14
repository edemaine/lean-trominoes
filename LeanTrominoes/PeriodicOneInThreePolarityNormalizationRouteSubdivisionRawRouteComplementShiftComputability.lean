/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementCanonicalShiftComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementShiftInputComputability

/-! # Clause-complement route-shift computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

def complementRawRouteShift {Input Variable : Type*}
    (period : Input → Nat)
    (input : (Input × ClauseMetadata Variable) ×
      (Nat × PeriodicLiteral Variable)) : Cell :=
  complementCanonicalShift
    ({ period := period input.1.1
       position := fun _ : Variable => (0, 0) } :
      PeriodicVariablePlacement Variable) input.2.2

theorem complementRawRouteShift_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec (complementRawRouteShift (Variable := Variable) period) := by
  exact ((complementCanonicalShift_primrec period periodPrimrec).comp
    complementRawRouteShiftInput_primrec).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
