/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterCounterExecution

/-! # Grouped record-counter data for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

def closeOutputField (data : TapeData) : TapeData :=
  { data with outputReverse := .atomEnd :: data.outputReverse }

def afterVertexClauseCounter (data : TapeData) : TapeData :=
  afterCounterData data data.clauseCount

def afterVertexLiteralFirstCounter (data : TapeData) : TapeData :=
  afterCounterData (afterVertexClauseCounter data) data.literalCount

def afterVertexCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterVertexLiteralFirstCounter data)
      data.literalCount)

@[simp] theorem afterVertexCounters_targets (data : TapeData) :
    (afterVertexCounters data).targets = data.targets := by
  rfl

theorem afterVertexCounters_eq (data : TapeData) :
    afterVertexCounters data =
      { data with
        scratch := []
        outputReverse :=
          .atomEnd :: (copiedOutput data.literalCount ++
            copiedOutput data.literalCount ++
              copiedOutput data.clauseCount ++ data.outputReverse) } := by
  simp only [afterVertexCounters, closeOutputField, afterCounterData,
    afterVertexLiteralFirstCounter, afterVertexClauseCounter,
    List.append_assoc]

def afterEdgeLiteralFirstCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterEdgeLiteralSecondCounter (data : TapeData) : TapeData :=
  afterCounterData (afterEdgeLiteralFirstCounter data) data.literalCount

def afterEdgeCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterEdgeLiteralSecondCounter data)
      data.literalCount)

@[simp] theorem afterEdgeCounters_targets (data : TapeData) :
    (afterEdgeCounters data).targets = data.targets := by
  rfl

theorem afterEdgeCounters_eq (data : TapeData) :
    afterEdgeCounters data =
      { data with
        scratch := []
        outputReverse :=
          .atomEnd :: (copiedOutput data.literalCount ++
            copiedOutput data.literalCount ++
              copiedOutput data.literalCount ++ data.outputReverse) } := by
  simp only [afterEdgeCounters, closeOutputField, afterCounterData,
    afterEdgeLiteralSecondCounter, afterEdgeLiteralFirstCounter,
    List.append_assoc]

def afterEdgeIndexCounter (data : TapeData) : TapeData :=
  closeOutputField (afterCounterData data data.edgeIndex)

@[simp] theorem afterEdgeIndexCounter_targets (data : TapeData) :
    (afterEdgeIndexCounter data).targets = data.targets := by
  rfl

theorem afterEdgeIndexCounter_eq (data : TapeData) :
    afterEdgeIndexCounter data =
      { data with
        scratch := []
        outputReverse :=
          .atomEnd ::
            (copiedOutput data.edgeIndex ++ data.outputReverse) } := by
  rfl

def afterSourceLiteralCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterSourceCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterSourceLiteralCounter data) data.clauseIndex)

@[simp] theorem afterSourceCounters_targets (data : TapeData) :
    (afterSourceCounters data).targets = data.targets := by
  rfl

theorem afterSourceCounters_eq (data : TapeData) :
    afterSourceCounters data =
      { data with
        scratch := []
        outputReverse :=
          .atomEnd :: (copiedOutput data.clauseIndex ++
            copiedOutput data.literalCount ++ data.outputReverse) } := by
  simp only [afterSourceCounters, closeOutputField, afterCounterData,
    afterSourceLiteralCounter, List.append_assoc]

def vertexCountersTime (data : TapeData) : Nat :=
  counterTime data.literalCount +
    (counterTime data.literalCount + counterTime data.clauseCount)

def edgeCountersTime (data : TapeData) : Nat :=
  counterTime data.literalCount +
    (counterTime data.literalCount + counterTime data.literalCount)

def sourceCountersTime (data : TapeData) : Nat :=
  counterTime data.clauseIndex + counterTime data.literalCount

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
