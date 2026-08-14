/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositionedMetadataComputability

/-! # Clause-complement route-shift input computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalizationPositioned

def complementRawRouteShiftInput {Input Variable : Type*}
    (input : (Input × ClauseMetadata Variable) ×
      (Nat × PeriodicLiteral Variable)) :
    Input × PeriodicLiteral Variable :=
  (input.1.1, input.2.2)

theorem complementRawRouteShiftInput_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable] :
    Primrec (complementRawRouteShiftInput (Input := Input)
      (Variable := Variable)) := by
  exact Primrec.pair
    (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
