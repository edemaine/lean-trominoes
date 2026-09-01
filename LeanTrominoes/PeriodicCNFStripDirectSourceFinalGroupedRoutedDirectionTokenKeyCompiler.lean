/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceDirectionBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Global incidence keys broadcast over routed direction tokens -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedRoutedDirectionKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Broadcast the routed incidence's global key across every direction token
and its terminating block delimiter. -/
def directSourceFinalGroupedRoutedDirectionTokenKeys
    (symbols : List encoding.Γ) : List Nat :=
  FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionTokens
      decider symbols)

/-- The routed key/token alignment is polynomial-time computable. -/
noncomputable def
    directSourceFinalGroupedRoutedDirectionTokenKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedRoutedDirectionTokenKeys decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedRoutedDirectionTokenKeys
    exact
      FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeysComputableInPolyTimeOf
        id
        (directSourceFinalGroupedRoutedIncidenceKeys decider)
        (directSourceFinalGroupedColoredOccurrenceDirectionTokens decider)
        (directSourceFinalGroupedRoutedIncidenceKeysComputableInPolyTime
          decider)
        (directSourceFinalGroupedColoredOccurrenceDirectionTokensComputableInPolyTime
          decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

@[simp] theorem directSourceFinalGroupedRoutedDirectionTokenKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedRoutedDirectionTokenKeys decider symbols).length =
      (directSourceFinalGroupedColoredOccurrenceDirectionTokens
        decider symbols).length := by
  unfold directSourceFinalGroupedRoutedDirectionTokenKeys
  exact FiniteAlphabetKeyedDelimitedBlockLookup.broadcastKeys_length _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
