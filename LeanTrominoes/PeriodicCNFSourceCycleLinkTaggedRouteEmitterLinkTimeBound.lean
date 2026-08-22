/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterScanExecutionData

/-! # Linear cost of one tagged cycle-link record pair -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem linkTime_scanTapeData_eq
    (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (linkIndex target : Nat) (tags : List Tag) (targets : List Nat)
    (outputReverse output : List OutputToken) (tag : Tag) :
    linkTime
        (scanTapeData input linkIndex tags (target :: targets)
          outputReverse output)
        target (UnaryFieldEncoderMachine.unaryFields targets) tag =
      8 * input.clauseCount + 28 * input.literalCount +
        14 * linkIndex + target + 56 := by
  simp only [linkTime, targetRecordTime, sourceTargetTime,
    sourcePrefixTime, sourceCountersTime, targetCountersTime,
    sourceVertexCountersTime, sourceEdgeCountersTime,
    sourceEdgeIndexCountersTime, sourceSourceCountersTime,
    targetVertexCountersTime, targetEdgeCountersTime,
    targetEdgeIndexCountersTime, targetSourceCountersTime,
    counterTime, scanTapeData, beginSourceRecordData,
    afterSourcePrefixData, afterSourceCounters,
    afterSourceVertexCounters, afterSourceVertexLiteralFirstCounter,
    afterSourceVertexClauseCounter, afterSourceEdgeCounters,
    afterSourceEdgeLiteralSecondCounter,
    afterSourceEdgeLiteralFirstCounter,
    afterSourceEdgeIndexCounters, afterSourceEdgeIndexFirstCounter,
    afterSourceEdgeIndexLiteralCounter, afterSourceSourceCounters,
    afterSourceSourceClauseCounter, afterSourceSourceLiteralCounter,
    beginTargetRecordData, afterFinishedSourceData,
    afterSourceTargetData, afterTargetVertexCounters,
    afterTargetVertexLiteralFirstCounter,
    afterTargetVertexClauseCounter, afterTargetEdgeCounters,
    afterTargetEdgeLiteralSecondCounter,
    afterTargetEdgeLiteralFirstCounter,
    afterTargetEdgeIndexCounters, afterTargetEdgeIndexFirstCounter,
    afterTargetEdgeIndexLiteralCounter, afterTargetSourceCounters,
    afterTargetSourceClauseCounter, afterTargetSourceLiteralCounter,
    afterCounterData, closeOutputField, addOutputUnitAndClose,
    List.length_replicate]
  omega

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
