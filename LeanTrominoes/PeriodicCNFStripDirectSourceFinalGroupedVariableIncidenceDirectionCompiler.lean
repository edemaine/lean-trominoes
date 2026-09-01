/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Complete grouped variable-incidence direction blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

abbrev VariableIncidencePrefixNormalizedToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

/-- Convert the finite-prefix compiler's normalized delimiter alphabet to
the generic direction-block alphabet used by the routed suffixes. -/
def variableIncidencePrefixDirectionTokenBlock :
    VariableIncidencePrefixNormalizedToken →
      List VariableIncidenceDirectionToken
  | .direction direction => [.value direction]
  | .routeEnd => [.blockEnd]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedVariableDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Independently delimited finite variable-prefix directions in the common
generic direction-block alphabet. -/
def directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
    (symbols : List encoding.Γ) : List VariableIncidenceDirectionToken :=
  (directSourceFinalGroupedVariableIncidencePrefixDirectionTokens
    decider symbols).flatMap variableIncidencePrefixDirectionTokenBlock

/-- Complete variable incidence directions obtained by joining every finite
prefix with its aligned empty or routed suffix. -/
noncomputable def directSourceFinalGroupedVariableIncidenceDirectionTokens
    (symbols : List encoding.Γ) : List VariableIncidenceDirectionToken :=
  FiniteAlphabetDelimitedBlockJoin.joined
    (directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
      decider symbols)
    (directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens
      decider symbols)

noncomputable def
    directSourceFinalGroupedVariableIncidencePrefixDelimitedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
        decider) := by
  unfold directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableIncidencePrefixDirectionTokensComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      variableIncidencePrefixDirectionTokenBlock)

/-- Pointwise delimited joining compiles all complete variable incidence
direction blocks in polynomial time. -/
noncomputable def
    directSourceFinalGroupedVariableIncidenceDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableIncidenceDirectionTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedVariableIncidenceDirectionTokens
    exact FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf
      id
      (directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens decider)
      (directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens decider)
      (directSourceFinalGroupedVariableIncidencePrefixDelimitedTokensComputableInPolyTime
        decider)
      (directSourceFinalGroupedVariableIncidenceSuffixDirectionTokensComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
