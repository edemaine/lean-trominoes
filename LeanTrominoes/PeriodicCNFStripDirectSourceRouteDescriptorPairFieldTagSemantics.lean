/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorPairFieldTagData
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorWordPairCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagSemantics

/-! # Exact semantics of direct-source descriptor-pair field tags -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourcePairFieldTagSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourcePairFieldTagSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled field-tag stream is exactly the canonical row-major square
of direct numeric descriptors. -/
theorem directSourceRouteDescriptorPairFieldTags_eq
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorPairFieldTags decider symbols =
      RouteDescriptorPairFieldTags.encodeDescriptorPairs
        (let descriptors :=
          numericRouteDescriptors (directSourceFormula decider symbols)
        descriptors ×ˢ descriptors) := by
  unfold directSourceRouteDescriptorPairFieldTags
  rw [directSourceRouteDescriptorWordPairs_eq_descriptorWordPairs]
  exact RouteDescriptorPairFieldTags.inputTokens_descriptorWordPairs _

end PeriodicCNFStripReduction
end LeanTrominoes

end
