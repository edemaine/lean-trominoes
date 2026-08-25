/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerPredicateData
import LeanTrominoes.SignedUnaryStrictLowerSemantics

/-! # Pointwise intersection of row-major Boolean matrices -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

theorem intersection_flatMap
    {Value : Type*} (values : List Value)
    (first second : Value → Value → Bool) :
    intersection
        (values.flatMap fun row => values.map (first row))
        (values.flatMap fun row => values.map (second row)) =
      values.flatMap fun row =>
        values.map fun column => first row column && second row column := by
  change SignedUnaryStrictLower.pairwise .conjunction
      (SignedUnaryStrictLower.matrix values first)
      (SignedUnaryStrictLower.matrix values second) = _
  rw [SignedUnaryStrictLower.pairwise_matrix]
  rfl

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
