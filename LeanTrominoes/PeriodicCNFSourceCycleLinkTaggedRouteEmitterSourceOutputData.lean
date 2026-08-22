/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterRecordExecutionData

/-! # Exact source-record counter output data -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def sourceVertexFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.literalCount ++
    copiedOutput data.literalCount ++ copiedOutput data.clauseCount)

def sourceEdgeFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.literalCount ++
    copiedOutput data.literalCount ++ copiedOutput data.literalCount)

def sourceEdgeIndexFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.linkIndex ++
    copiedOutput data.linkIndex ++ copiedOutput data.literalCount)

def sourceSourceFieldReverse (data : TapeData) : List OutputToken :=
  .atomEnd :: (copiedOutput data.linkIndex ++
    copiedOutput data.clauseCount ++ copiedOutput data.literalCount)

def sourceCounterPrefixReverse (data : TapeData) : List OutputToken :=
  sourceSourceFieldReverse data ++ sourceEdgeIndexFieldReverse data ++
    sourceEdgeFieldReverse data ++ sourceVertexFieldReverse data ++
      [.clauseMarker]

def sourceCounterPrefix (data : TapeData) : List OutputToken :=
  (sourceCounterPrefixReverse data).reverse

theorem afterSourceVertexCounters_eq (data : TapeData) :
    afterSourceVertexCounters data =
      { data with
        scratch := []
        outputReverse :=
          sourceVertexFieldReverse data ++ data.outputReverse } := by
  simp only [afterSourceVertexCounters, closeOutputField,
    afterSourceVertexLiteralFirstCounter,
    afterSourceVertexClauseCounter, afterCounterData,
    sourceVertexFieldReverse, List.cons_append, List.append_assoc]

theorem afterSourceEdgeCounters_eq (data : TapeData) :
    afterSourceEdgeCounters data =
      { data with
        scratch := []
        outputReverse :=
          sourceEdgeFieldReverse data ++ data.outputReverse } := by
  simp only [afterSourceEdgeCounters, closeOutputField,
    afterSourceEdgeLiteralSecondCounter,
    afterSourceEdgeLiteralFirstCounter, afterCounterData,
    sourceEdgeFieldReverse, List.cons_append, List.append_assoc]

theorem afterSourceEdgeIndexCounters_eq (data : TapeData) :
    afterSourceEdgeIndexCounters data =
      { data with
        scratch := []
        outputReverse :=
          sourceEdgeIndexFieldReverse data ++ data.outputReverse } := by
  simp only [afterSourceEdgeIndexCounters, closeOutputField,
    afterSourceEdgeIndexFirstCounter,
    afterSourceEdgeIndexLiteralCounter, afterCounterData,
    sourceEdgeIndexFieldReverse, List.cons_append, List.append_assoc]

theorem afterSourceSourceCounters_eq (data : TapeData) :
    afterSourceSourceCounters data =
      { data with
        scratch := []
        outputReverse :=
          sourceSourceFieldReverse data ++ data.outputReverse } := by
  simp only [afterSourceSourceCounters, closeOutputField,
    afterSourceSourceClauseCounter,
    afterSourceSourceLiteralCounter, afterCounterData,
    sourceSourceFieldReverse, List.cons_append, List.append_assoc]

theorem afterSourcePrefixData_eq (data : TapeData) :
    afterSourcePrefixData data =
      { data with
        scratch := []
        outputReverse :=
          sourceCounterPrefixReverse data ++ data.outputReverse } := by
  simp only [afterSourcePrefixData, afterSourceCounters,
    afterSourceSourceCounters_eq, afterSourceEdgeIndexCounters_eq,
    afterSourceEdgeCounters_eq, afterSourceVertexCounters_eq,
    beginSourceRecordData, sourceCounterPrefixReverse,
    sourceSourceFieldReverse, sourceEdgeIndexFieldReverse,
    sourceEdgeFieldReverse, sourceVertexFieldReverse,
    List.cons_append, List.nil_append, List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
