/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierFallbackRouteTailRecordData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Normalized.PeriodicOrthocrossingCarrierNormalizedFallbackRouteTailRecordBlockData

/-! # Direct-source normalized retained-carrier fallback record data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Direct carrier record blocks with unchanged profiles and canonical
normalized complete route words. -/
def directSourceFinalCarrierNormalizedFallbackRecordBlocks
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Block :=
  CarrierNormalizedFallbackRouteTailRecords.blocks
    (directSourceFinalCarrierFallbackRecordGeometries decider symbols)
    (directSourceFinalCarrierOccurrenceSlots decider symbols)

def directSourceFinalCarrierNormalizedFallbackRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordBatchFormatter.tokens
    (directSourceFinalCarrierNormalizedFallbackRecordBlocks decider symbols)

def directSourceFinalCarrierNormalizedFallbackRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.records
    (directSourceFinalCarrierNormalizedFallbackRecordBlocks decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
