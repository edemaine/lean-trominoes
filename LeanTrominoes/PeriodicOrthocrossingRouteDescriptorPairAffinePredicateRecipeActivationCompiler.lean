/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationCompiler

/-! # Compiler composition for affine-predicate recipe activations -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairCarrierKeyWordRecipes

/-- Evaluate a fixed predicate family and expand its truth values across the
corresponding fixed recipe blocks. -/
def predicateListExpandedActives (predicates : List Predicate)
    (blocks : List (List Recipe))
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  compiledExpandedActives blocks
    (predicateListTruthValues predicates tokens)

/-- Fixed affine predicates followed by fixed recipe-block expansion are
polynomial-time computable. -/
noncomputable def predicateListExpandedActivesComputableInPolyTime
    (predicates : List Predicate) (blocks : List (List Recipe)) :
    TM2ComputableInPolyTime id id
      (predicateListExpandedActives predicates blocks) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (predicateListTruthValuesComputableInPolyTime predicates)
    (compiledExpandedActivesComputableInPolyTime blocks)
  unfold predicateListExpandedActives
  exact composed

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
