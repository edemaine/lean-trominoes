/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionRawRouteComplementRefinedTranslationComputability

/-! # Complement canonical-shift computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The clause-anchor correction for a complement route is primitive
recursive in the source placement period and literal offset. -/
theorem complementCanonicalShift_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec fun input : Input × PeriodicLiteral Variable =>
      complementCanonicalShift
        ({ period := period input.1
           position := fun _ : Variable => (0, 0) } :
          PeriodicVariablePlacement Variable) input.2 := by
  exact (Computability.cell_sub_primrec.comp
    (Primrec.const ((0, 0) : Cell))
    (complementRefinedTranslation_primrec period periodPrimrec)).of_eq
      fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
