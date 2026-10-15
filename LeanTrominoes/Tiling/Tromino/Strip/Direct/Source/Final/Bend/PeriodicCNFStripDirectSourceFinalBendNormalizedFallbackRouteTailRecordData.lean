/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendFallbackRouteTailRecordData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Bend.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockData

/-! # Direct-source normalized retained-bend fallback record data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
