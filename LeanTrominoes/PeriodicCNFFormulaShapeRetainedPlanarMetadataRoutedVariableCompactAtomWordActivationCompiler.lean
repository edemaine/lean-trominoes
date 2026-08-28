/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateRecipeActivationCompiler

/-! # Compiler for routed-variable compact-word activations -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing

/-- One compiled activation bit per flattened routed-variable word recipe. -/
def routedVariableCompactAtomWordExpandedActives
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  predicateListExpandedActives routedVariableCompactAtomWordPredicates
    routedVariableCompactAtomWordRecipeBlocks tokens

/-- The fixed routed-variable recipe activation word is polynomial-time
computable. -/
noncomputable def
    routedVariableCompactAtomWordExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      routedVariableCompactAtomWordExpandedActives := by
  exact predicateListExpandedActivesComputableInPolyTime
    routedVariableCompactAtomWordPredicates
    routedVariableCompactAtomWordRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
