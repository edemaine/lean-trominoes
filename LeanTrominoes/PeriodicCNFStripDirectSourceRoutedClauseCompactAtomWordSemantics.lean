/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFRouteDescriptorSourceTerminalCompactAtomWordPresentation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordFamilies
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCompactAtomWordSemantics

/-! # Direct routed-clause compact atom-word semantics -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRoutedClauseCompactWordSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRoutedClauseCompactWordSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The decoded physical stream is the semantic descriptor-word stream. -/
theorem directSourceTerminalCompactAtomWords_eq_descriptors
    (symbols : List encoding.Γ) :
    directSourceTerminalCompactAtomWords decider symbols =
      RouteDescriptorSourceTerminalCompactWords.words
        (numericRouteDescriptors
          (directSourceFormula decider symbols)) := by
  unfold directSourceTerminalCompactAtomWords
    directSourceTerminalCompactAtomWordTokens
    directSourceRouteDescriptorScanTokens
    directSourceRouteDescriptorTokens
  rw [RouteDescriptorScanTokens.normalize_routeDescriptorTokens]
  rw [RouteDescriptorSourceTerminalCompactWords.tokens_encode]
  simp

/-- Delimited target carrying exactly the routed-clause family block. -/
def directSourceFinalCompactRoutedClauseAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  ⟨directSourceFinalCompactRoutedClauseAtomWordBlock decider symbols⟩

/-- The descriptor source-terminal stream is exactly the routed-clause block
of the final compact occurrence column. -/
theorem directSourceTerminalCompactAtomWords_eq_routedClauseBlock
    (symbols : List encoding.Γ) :
    directSourceTerminalCompactAtomWords decider symbols =
      directSourceFinalCompactRoutedClauseAtomWords decider symbols := by
  rw [directSourceTerminalCompactAtomWords_eq_descriptors]
  unfold directSourceFinalCompactRoutedClauseAtomWords
    directSourceFinalCompactRoutedClauseAtomWordBlock
    directThreeCNFSourceFormula
  dsimp only
  rw [← directSourceFormula_eq_threeSATThree]

end PeriodicCNFStripReduction
end LeanTrominoes

end
