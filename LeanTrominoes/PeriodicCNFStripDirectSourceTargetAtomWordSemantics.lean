/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceTargetAtomWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordSemantics

/-! # Exact semantics of direct-source target-vertex atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directTargetAtomWordSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directTargetAtomWordSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The physical projection is exactly the canonical encoding of all direct
source target-index words. -/
theorem directSourceTargetAtomWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceTargetAtomWordTokens decider symbols =
      DelimitedBinaryWords.encode
        (directSourceTargetAtomWords decider symbols) := by
  unfold directSourceTargetAtomWords
  have physical_eq :
      directSourceTargetAtomWordTokens decider symbols =
        DelimitedBinaryWords.encode
          (RouteDescriptorTargetAtomWords.words
            (numericRouteDescriptors
              (directSourceFormula decider symbols))) := by
    unfold directSourceTargetAtomWordTokens
      directSourceRouteDescriptorScanTokens
      directSourceRouteDescriptorTokens
    rw [RouteDescriptorScanTokens.normalize_routeDescriptorTokens]
    exact RouteDescriptorTargetAtomWords.tokens_encode _
  rw [physical_eq]
  simp

end PeriodicCNFStripReduction
end LeanTrominoes

end
