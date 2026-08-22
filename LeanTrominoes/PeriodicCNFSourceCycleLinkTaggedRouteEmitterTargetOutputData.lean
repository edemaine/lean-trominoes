/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordExecutionData

/-! # Exact target-record counter output data -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def targetVertexFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.literalCount ++
    copiedOutput data.literalCount ++ copiedOutput data.clauseCount)

def targetEdgeFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.literalCount ++
    copiedOutput data.literalCount ++ copiedOutput data.literalCount)

def targetEdgeIndexFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: .atomUnit :: (copiedOutput data.linkIndex ++
    copiedOutput data.linkIndex ++ copiedOutput data.literalCount)

def targetSourceFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.linkIndex ++
    copiedOutput data.clauseCount ++ copiedOutput data.literalCount)

def targetTargetIndexReverse (data : TapeData) : List OutputToken :=
  copiedOutput data.linkIndex

def targetCounterPrefixReverse (data : TapeData) : List OutputToken :=
  targetTargetIndexReverse data ++ targetSourceFieldReverse data ++
    targetEdgeIndexFieldReverse data ++ targetEdgeFieldReverse data ++
      targetVertexFieldReverse data ++ [.clauseMarker]

def targetCounterPrefix (data : TapeData) : List OutputToken :=
  (targetCounterPrefixReverse data).reverse

theorem afterTargetVertexCounters_eq (data : TapeData) :
    afterTargetVertexCounters data =
      { data with
        scratch := []
        outputReverse :=
          targetVertexFieldReverse data ++ data.outputReverse } := by
  simp only [afterTargetVertexCounters, closeOutputField,
    afterTargetVertexLiteralFirstCounter,
    afterTargetVertexClauseCounter, afterCounterData,
    targetVertexFieldReverse, List.cons_append, List.append_assoc]

theorem afterTargetEdgeCounters_eq (data : TapeData) :
    afterTargetEdgeCounters data =
      { data with
        scratch := []
        outputReverse :=
          targetEdgeFieldReverse data ++ data.outputReverse } := by
  simp only [afterTargetEdgeCounters, closeOutputField,
    afterTargetEdgeLiteralSecondCounter,
    afterTargetEdgeLiteralFirstCounter, afterCounterData,
    targetEdgeFieldReverse, List.cons_append, List.append_assoc]

theorem afterTargetEdgeIndexCounters_eq (data : TapeData) :
    afterTargetEdgeIndexCounters data =
      { data with
        scratch := []
        outputReverse :=
          targetEdgeIndexFieldReverse data ++ data.outputReverse } := by
  simp only [afterTargetEdgeIndexCounters, addOutputUnitAndClose,
    afterTargetEdgeIndexFirstCounter,
    afterTargetEdgeIndexLiteralCounter, afterCounterData,
    targetEdgeIndexFieldReverse, List.cons_append, List.append_assoc]

theorem afterTargetSourceCounters_eq (data : TapeData) :
    afterTargetSourceCounters data =
      { data with
        scratch := []
        outputReverse :=
          targetSourceFieldReverse data ++ data.outputReverse } := by
  simp only [afterTargetSourceCounters, closeOutputField,
    afterTargetSourceClauseCounter,
    afterTargetSourceLiteralCounter, afterCounterData,
    targetSourceFieldReverse, List.cons_append, List.append_assoc]

theorem afterTargetTargetIndexCounter_eq (data : TapeData) :
    afterTargetTargetIndexCounter data =
      { data with
        scratch := []
        outputReverse :=
          targetTargetIndexReverse data ++ data.outputReverse } := by
  simp only [afterTargetTargetIndexCounter, afterCounterData,
    targetTargetIndexReverse]

theorem afterTargetPrefixData_eq (data : TapeData) :
    afterTargetPrefixData data =
      { data with
        scratch := []
        outputReverse :=
          targetCounterPrefixReverse data ++ data.outputReverse } := by
  simp only [afterTargetPrefixData, afterTargetCounters,
    afterTargetTargetIndexCounter_eq, afterTargetSourceCounters_eq,
    afterTargetEdgeIndexCounters_eq, afterTargetEdgeCounters_eq,
    afterTargetVertexCounters_eq, beginTargetRecordData,
    targetCounterPrefixReverse, targetTargetIndexReverse,
    targetSourceFieldReverse, targetEdgeIndexFieldReverse,
    targetEdgeFieldReverse, targetVertexFieldReverse,
    List.cons_append, List.nil_append, List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
