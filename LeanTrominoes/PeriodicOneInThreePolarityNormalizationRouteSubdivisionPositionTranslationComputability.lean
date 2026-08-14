/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionBasicComputability

/-! # Refined-placement translation computability -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- A semantic offset translated by the refined placement is primitive
recursive in the unrefined period. -/
theorem refinedPlacement_translation_primrec
    {Input : Type*} [Primcodable Input]
    (period : Input → Nat) (periodPrimrec : Primrec period) :
    Primrec fun input : Input × Cell =>
      (refinedPlacement
        ({ period := period input.1
           position := fun _ : Unit => (0, 0) } :
          PeriodicVariablePlacement Unit)).translation input.2 := by
  have refinedPeriod : Primrec fun input : Input × Cell =>
      refinementFactor * period input.1 :=
    Primrec.nat_mul.comp (Primrec.const refinementFactor)
      (periodPrimrec.comp Primrec.fst)
  exact (Computability.cell_scale_primrec.comp
    (Computability.int_ofNat_primrec.comp refinedPeriod)
    Primrec.snd).of_eq fun _ => rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
