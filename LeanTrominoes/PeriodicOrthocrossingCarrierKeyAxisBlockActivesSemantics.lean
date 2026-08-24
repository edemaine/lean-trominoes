/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedAxisUnaryFieldsCandidateBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationData

/-! # Recipe/axis block activation alignment -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The recipe and generic axis-block expanders agree whenever corresponding
blocks have equal lengths. -/
theorem expandedActives_eq_axisBlockActives_of_forall₂_length
    (actives : List Bool)
    {blocks : List (List
      RouteDescriptorPairCarrierKeyWordRecipes.Recipe)}
    {axisBlocks : List (List Bool)}
    (aligned : List.Forall₂
      (fun block axes => block.length = axes.length)
      blocks axisBlocks) :
    RouteDescriptorPairCarrierKeyWordRecipes.expandedActives
        actives blocks =
      FixedAxisUnaryFields.blockActives actives axisBlocks := by
  induction aligned generalizing actives with
  | nil => simp [RouteDescriptorPairCarrierKeyWordRecipes.expandedActives,
      FixedAxisUnaryFields.blockActives]
  | cons head tail induction =>
      cases actives with
      | nil => simp [RouteDescriptorPairCarrierKeyWordRecipes.expandedActives,
          FixedAxisUnaryFields.blockActives]
      | cons active actives =>
          simp only [RouteDescriptorPairCarrierKeyWordRecipes.expandedActives,
            FixedAxisUnaryFields.blockActives]
          rw [head, induction actives]

end LeanTrominoes.PeriodicOrthocrossing
