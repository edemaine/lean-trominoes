/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.PeriodicCNFStripDirectFinalColoredOccurrenceRequestData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceEndpointFrameCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Direct compiler for aligned colored occurrence requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace DirectFinalColoredOccurrenceRequest

open Computability Turing

noncomputable def openingBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id openingBlocks :=
  FiniteBlockTransducer.computableInPolyTime openingBlock

noncomputable def trailingBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id trailingBlocks :=
  FiniteBlockTransducer.computableInPolyTime trailingBlock

noncomputable def routedBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id routedBlocks :=
  FiniteBlockTransducer.computableInPolyTime routedBlockToken

end DirectFinalColoredOccurrenceRequest

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalColoredOccurrenceRequestStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One end-delimited complete input for the established routed-occurrence
compiler per colored final occurrence. -/
def directSourceFinalColoredOccurrenceRequestTokens
    (symbols : List encoding.Γ) :
    List DirectFinalColoredOccurrenceRequest.Token :=
  DirectFinalColoredOccurrenceRequest.output
    (directSourceFinalOccurrenceEndpointFrames decider symbols)
    (directSourceFinalColoredRoutedRequestBlockTokens decider symbols)

/-- Endpoint openings, variable-length routed words, and endpoint trailings
are aligned by two verified block joins. -/
noncomputable def
    directSourceFinalColoredOccurrenceRequestTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalColoredOccurrenceRequestTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    let openings := TM2CompositionMachine.computableInPolyTime
      (directSourceFinalOccurrenceEndpointFramesComputableInPolyTime decider)
      DirectFinalColoredOccurrenceRequest.openingBlocksComputableInPolyTime
    let routes := TM2CompositionMachine.computableInPolyTime
      (directSourceFinalColoredRoutedRequestBlockTokensComputableInPolyTime
        decider)
      DirectFinalColoredOccurrenceRequest.routedBlocksComputableInPolyTime
    let opened :=
      FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf id
        (fun symbols =>
          DirectFinalColoredOccurrenceRequest.openingBlocks
            (directSourceFinalOccurrenceEndpointFrames decider symbols))
        (fun symbols =>
          DirectFinalColoredOccurrenceRequest.routedBlocks
            (directSourceFinalColoredRoutedRequestBlockTokens decider symbols))
        openings routes
    let trailings := TM2CompositionMachine.computableInPolyTime
      (directSourceFinalOccurrenceEndpointFramesComputableInPolyTime decider)
      DirectFinalColoredOccurrenceRequest.trailingBlocksComputableInPolyTime
    exact FiniteAlphabetDelimitedBlockJoin.joinedComputableInPolyTimeOf id
      (fun symbols => DirectFinalColoredOccurrenceRequest.opened
        (directSourceFinalOccurrenceEndpointFrames decider symbols)
        (directSourceFinalColoredRoutedRequestBlockTokens decider symbols))
      (fun symbols =>
        DirectFinalColoredOccurrenceRequest.trailingBlocks
          (directSourceFinalOccurrenceEndpointFrames decider symbols))
      opened trailings
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
