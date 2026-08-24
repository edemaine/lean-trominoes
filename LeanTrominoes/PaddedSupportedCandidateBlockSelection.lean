/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActivity
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockData

/-! # Fixed slots versus compact affine block selection -/

namespace LeanTrominoes.PaddedSupportedCandidateBlocks

open PeriodicOrthocrossing.RouteDescriptorPairAffine

variable {Value : Type}

/-- The compact active-value stream is definitionally the existing affine
truth-block selector applied to the template values. -/
theorem activeValues_eq_selectTruthBlocks
    (actives : List Bool) (blocks : List (List (Template Value))) :
    activeValues actives blocks =
      selectTruthBlocks
        (blocks.map fun block => block.map Template.value) actives := by
  induction actives generalizing blocks with
  | nil => cases blocks <;> rfl
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          cases active <;>
            simp [activeValues, selectTruthBlocks, induction]

end LeanTrominoes.PaddedSupportedCandidateBlocks
