/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationData

/-! # Compiler for flattened carrier-key recipe activations -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

open Computability Turing

/-- Finite-control expansion of one block activation into one bit per recipe. -/
def compiledExpandedActives (blocks : List (List Recipe))
    (actives : List Bool) : List Bool :=
  FixedLengthWordEvaluator.output blocks.length
    (fun stored => expandedActives stored blocks) actives

/-- Exact-length activation inputs expand to their semantic flattened word. -/
theorem compiledExpandedActives_eq
    (blocks : List (List Recipe)) (actives : List Bool)
    (lengthEq : actives.length = blocks.length) :
    compiledExpandedActives blocks actives =
      expandedActives actives blocks := by
  exact FixedLengthWordEvaluator.output_eq_of_length_eq
    blocks.length (fun stored => expandedActives stored blocks)
    actives lengthEq

/-- Every fixed recipe-block family has a polynomial-time activation
expander. -/
noncomputable def compiledExpandedActivesComputableInPolyTime
    (blocks : List (List Recipe)) :
    TM2ComputableInPolyTime id id (compiledExpandedActives blocks) :=
  FixedLengthWordEvaluator.computableInPolyTime blocks.length
    (fun stored => expandedActives stored blocks)

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
