/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceDirectionBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.UnaryFieldThreeBlockOrdinalCompiler

/-! # Colored occurrence directions in variable-major order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance
    directFinalGroupedColoredOccurrenceDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Occurrence-major colored block ordinals regrouped by identity and stable
occurrence rank. -/
def directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldThreeBlockOrdinals.values
    (directSourceFinalGroupedOccurrenceIndices decider symbols)

/-- Complete red/green/blue occurrence-direction blocks selected in
variable-major and stable-rank-minor order. -/
def directSourceFinalGroupedColoredOccurrenceDirectionTokens
    (symbols : List encoding.Γ) :
    List DirectFinalColoredOccurrenceDirectionToken :=
  FiniteAlphabetIndexedDelimitedBlockLookup.selected
    (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
      decider symbols)
    (directSourceFinalColoredOccurrenceDirectionTokens decider symbols)

noncomputable def
    directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinalsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
        decider) := by
  unfold directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedOccurrenceIndicesComputableInPolyTime decider)
    UnaryFieldThreeBlockOrdinals.computableInPolyTime

/-- Indexed delimited-block lookup compiles the complete reordered colored
direction blocks in polynomial time. -/
noncomputable def
    directSourceFinalGroupedColoredOccurrenceDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedColoredOccurrenceDirectionTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedColoredOccurrenceDirectionTokens
    exact
      FiniteAlphabetIndexedDelimitedBlockLookup.selectedComputableInPolyTimeOf
        id
        (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinals
          decider)
        (directSourceFinalColoredOccurrenceDirectionTokens decider)
        (directSourceFinalGroupedColoredOccurrenceDirectionBlockOrdinalsComputableInPolyTime
          decider)
        (directSourceFinalColoredOccurrenceDirectionTokensComputableInPolyTime
          decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
