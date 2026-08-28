/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorSourceTerminalCompactWordSemantics

/-! # Exact semantics of direct-source source-terminal compact words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceTerminalCompactSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceTerminalCompactSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceTerminalCompactAtomWordTokens_eq_encode
    (symbols : List encoding.Γ) :
    directSourceTerminalCompactAtomWordTokens decider symbols =
      DelimitedBinaryWords.encode
        (directSourceTerminalCompactAtomWords decider symbols) := by
  unfold directSourceTerminalCompactAtomWords
  have physicalEq :
      directSourceTerminalCompactAtomWordTokens decider symbols =
        DelimitedBinaryWords.encode
          (RouteDescriptorSourceTerminalCompactWords.words
            (numericRouteDescriptors
              (directSourceFormula decider symbols))) := by
    unfold directSourceTerminalCompactAtomWordTokens
      directSourceRouteDescriptorScanTokens
      directSourceRouteDescriptorTokens
    rw [RouteDescriptorScanTokens.normalize_routeDescriptorTokens]
    exact RouteDescriptorSourceTerminalCompactWords.tokens_encode _
  rw [physicalEq]
  simp

end PeriodicCNFStripReduction
end LeanTrominoes

end
