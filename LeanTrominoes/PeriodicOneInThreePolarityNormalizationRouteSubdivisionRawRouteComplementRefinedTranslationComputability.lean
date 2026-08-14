/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionPositionTranslationComputability
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementRefinedTranslationInputComputability

/-! # Complement refined-translation computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

def complementRefinedTranslation {Input Variable : Type*}
    (period : Input → Nat) (input : Input × PeriodicLiteral Variable) : Cell :=
  (refinedPlacement
    ({ period := period input.1
       position := fun _ : Unit => (0, 0) } :
      PeriodicVariablePlacement Unit)).translation input.2.offset

theorem complementRefinedTranslation_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec (complementRefinedTranslation (Variable := Variable) period) := by
  exact ((refinedPlacement_translation_primrec period periodPrimrec).comp
    complementRefinedTranslationInput_primrec).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
