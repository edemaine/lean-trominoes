/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateRecipeActivationCompiler

/-! # Compiler for affine bend compact-word recipe activations -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing

/-- One compiled activation bit per flattened compact bend-word recipe. -/
def bendCompactAtomWordExpandedActives
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  predicateListExpandedActives bendDescriptorPredicates
    bendCompactAtomWordRecipeBlocks tokens

/-- The fixed bend recipe activation word is polynomial-time computable. -/
noncomputable def bendCompactAtomWordExpandedActivesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      bendCompactAtomWordExpandedActives := by
  exact predicateListExpandedActivesComputableInPolyTime
    bendDescriptorPredicates bendCompactAtomWordRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
