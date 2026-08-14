/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNF

/-! # Complement refined-translation input computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

def complementRefinedTranslationInput {Input Variable : Type*}
    (input : Input × PeriodicLiteral Variable) : Input × Cell :=
  (input.1, input.2.offset)

theorem complementRefinedTranslationInput_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable] :
    Primrec (complementRefinedTranslationInput (Input := Input)
      (Variable := Variable)) := by
  have offset : Primrec fun literal : PeriodicLiteral Variable =>
      literal.offset :=
    (Primrec.fst.comp (Primrec.snd.comp
      PeriodicLiteral.equivData_primrec)).of_eq fun _ => rfl
  exact Primrec.pair Primrec.fst
    (offset.comp Primrec.snd)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
