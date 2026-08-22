/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterExecution

/-! # Grouped record-counter data for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def closeOutputField (data : TapeData) : TapeData :=
  { data with outputReverse := .atomEnd :: data.outputReverse }

def addOutputUnitAndClose (data : TapeData) : TapeData :=
  { data with
    outputReverse := .atomEnd :: .atomUnit :: data.outputReverse }

def afterSourceVertexClauseCounter (data : TapeData) : TapeData :=
  afterCounterData data data.clauseCount

def afterSourceVertexLiteralFirstCounter (data : TapeData) : TapeData :=
  afterCounterData (afterSourceVertexClauseCounter data) data.literalCount

def afterSourceVertexCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterSourceVertexLiteralFirstCounter data)
      data.literalCount)

def afterSourceEdgeLiteralFirstCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterSourceEdgeLiteralSecondCounter (data : TapeData) : TapeData :=
  afterCounterData (afterSourceEdgeLiteralFirstCounter data)
    data.literalCount

def afterSourceEdgeCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterSourceEdgeLiteralSecondCounter data)
      data.literalCount)

def afterSourceEdgeIndexLiteralCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterSourceEdgeIndexFirstCounter (data : TapeData) : TapeData :=
  afterCounterData (afterSourceEdgeIndexLiteralCounter data) data.linkIndex

def afterSourceEdgeIndexCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterSourceEdgeIndexFirstCounter data) data.linkIndex)

def afterSourceSourceLiteralCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterSourceSourceClauseCounter (data : TapeData) : TapeData :=
  afterCounterData (afterSourceSourceLiteralCounter data) data.clauseCount

def afterSourceSourceCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterSourceSourceClauseCounter data) data.linkIndex)

def afterTargetVertexClauseCounter (data : TapeData) : TapeData :=
  afterCounterData data data.clauseCount

def afterTargetVertexLiteralFirstCounter (data : TapeData) : TapeData :=
  afterCounterData (afterTargetVertexClauseCounter data) data.literalCount

def afterTargetVertexCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterTargetVertexLiteralFirstCounter data)
      data.literalCount)

def afterTargetEdgeLiteralFirstCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterTargetEdgeLiteralSecondCounter (data : TapeData) : TapeData :=
  afterCounterData (afterTargetEdgeLiteralFirstCounter data)
    data.literalCount

def afterTargetEdgeCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterTargetEdgeLiteralSecondCounter data)
      data.literalCount)

def afterTargetEdgeIndexLiteralCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterTargetEdgeIndexFirstCounter (data : TapeData) : TapeData :=
  afterCounterData (afterTargetEdgeIndexLiteralCounter data) data.linkIndex

def afterTargetEdgeIndexCounters (data : TapeData) : TapeData :=
  addOutputUnitAndClose
    (afterCounterData (afterTargetEdgeIndexFirstCounter data) data.linkIndex)

def afterTargetSourceLiteralCounter (data : TapeData) : TapeData :=
  afterCounterData data data.literalCount

def afterTargetSourceClauseCounter (data : TapeData) : TapeData :=
  afterCounterData (afterTargetSourceLiteralCounter data) data.clauseCount

def afterTargetSourceCounters (data : TapeData) : TapeData :=
  closeOutputField
    (afterCounterData (afterTargetSourceClauseCounter data) data.linkIndex)

def afterTargetTargetIndexCounter (data : TapeData) : TapeData :=
  afterCounterData data data.linkIndex

def sourceVertexCountersTime (data : TapeData) : Nat :=
  counterTime data.literalCount +
    (counterTime data.literalCount + counterTime data.clauseCount)

def sourceEdgeCountersTime (data : TapeData) : Nat :=
  counterTime data.literalCount +
    (counterTime data.literalCount + counterTime data.literalCount)

def sourceEdgeIndexCountersTime (data : TapeData) : Nat :=
  counterTime data.linkIndex +
    (counterTime data.linkIndex + counterTime data.literalCount)

def sourceSourceCountersTime (data : TapeData) : Nat :=
  counterTime data.linkIndex +
    (counterTime data.clauseCount + counterTime data.literalCount)

def targetVertexCountersTime (data : TapeData) : Nat :=
  counterTime data.literalCount +
    (counterTime data.literalCount + counterTime data.clauseCount)

def targetEdgeCountersTime (data : TapeData) : Nat :=
  counterTime data.literalCount +
    (counterTime data.literalCount + counterTime data.literalCount)

def targetEdgeIndexCountersTime (data : TapeData) : Nat :=
  counterTime data.linkIndex +
    (counterTime data.linkIndex + counterTime data.literalCount)

def targetSourceCountersTime (data : TapeData) : Nat :=
  counterTime data.linkIndex +
    (counterTime data.clauseCount + counterTime data.literalCount)

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
