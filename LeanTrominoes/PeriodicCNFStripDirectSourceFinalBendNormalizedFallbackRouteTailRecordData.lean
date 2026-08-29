/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRouteTailRecordData
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockData

/-! # Direct-source normalized retained-bend fallback record data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendNormalizedFallbackRecordDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Direct bend record blocks with unchanged profiles and canonical normalized
complete route words. -/
def directSourceFinalBendNormalizedFallbackRecordBlocks
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Block :=
  BendNormalizedFallbackRouteTailRecords.blocks
    (directSourceFinalBendFallbackRecordGeometries decider symbols)
    (directSourceFinalBendOccurrenceSlots decider symbols)

def directSourceFinalBendNormalizedFallbackRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordBatchFormatter.tokens
    (directSourceFinalBendNormalizedFallbackRecordBlocks decider symbols)

def directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.records
    (directSourceFinalBendNormalizedFallbackRecordBlocks decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
