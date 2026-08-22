/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordExecutionData

/-! # Exact one-record output data for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def vertexFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.literalCount ++
    copiedOutput data.literalCount ++ copiedOutput data.clauseCount)

def edgeFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.literalCount ++
    copiedOutput data.literalCount ++ copiedOutput data.literalCount)

def edgeIndexFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: copiedOutput data.edgeIndex

def sourceFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd ::
    (copiedOutput data.clauseIndex ++ copiedOutput data.literalCount)

/-- The reversed first four fields together with the leading record marker. -/
def recordCounterPrefixReverse (data : TapeData) : List OutputToken :=
  sourceFieldReverse data ++ edgeIndexFieldReverse data ++
    edgeFieldReverse data ++ vertexFieldReverse data ++ [.clauseMarker]

def recordCounterPrefix (data : TapeData) : List OutputToken :=
  (recordCounterPrefixReverse data).reverse

/-- The complete forward token block emitted for one occurrence record. -/
def emittedRecordTokens (data : TapeData) (targetCount : Nat)
    (literalIndex : Fin 3) (currentNext anchorNext : Bool) :
    List OutputToken :=
  recordCounterPrefix data ++ CountedUnaryFieldTokens.field targetCount ++
    fixedSuffix literalIndex currentNext anchorNext

theorem afterRecordCounters_beginRecordData_eq (data : TapeData) :
    afterRecordCounters (beginRecordData data) =
      { data with
        scratch := []
        outputReverse :=
          recordCounterPrefixReverse data ++ data.outputReverse } := by
  simp only [afterRecordCounters, afterSourceCounters_eq,
    afterEdgeIndexCounter_eq, afterEdgeCounters_eq,
    afterVertexCounters_eq, beginRecordData, recordCounterPrefixReverse,
    sourceFieldReverse, edgeIndexFieldReverse, edgeFieldReverse,
    vertexFieldReverse, List.cons_append, List.nil_append,
    List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
