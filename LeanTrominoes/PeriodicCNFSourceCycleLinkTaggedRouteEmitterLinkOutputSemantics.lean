/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterLinkExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceRecordOutputSemantics
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetRecordOutputSemantics

/-! # Exact one-link output semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def emittedLinkTokens (data : TapeData) (targetCount : Nat)
    (tag : Tag) : List OutputToken :=
  sourceRecordTokens data targetCount tag ++ targetRecordTokens data tag

theorem emittedLinkTokens_eq_linkTokens
    (input : SourceCycleLinkTaggedRouteEmitter.Input)
    (data : TapeData) (linkIndex targetCount : Nat) (tag : Tag)
    (clauseEq : data.clauseCount.length = input.clauseCount)
    (literalEq : data.literalCount.length = input.literalCount)
    (indexEq : data.linkIndex.length = linkIndex) :
    emittedLinkTokens data targetCount tag =
      SourceCycleLinkTaggedRouteEmitter.linkTokens
        input linkIndex targetCount tag := by
  rw [emittedLinkTokens,
    sourceRecordTokens_eq_countedFieldBlock,
    targetRecordTokens_eq_countedFieldBlock]
  simp only [SourceCycleLinkTaggedRouteEmitter.linkTokens,
    SourceCycleLinkTaggedRouteEmitter.sourceFields,
    SourceCycleLinkTaggedRouteEmitter.targetFields]
  rw [clauseEq, literalEq, indexEq]

theorem afterLinkData_eq (data : TapeData) (targetCount : Nat)
    (remainingTargets : List UnarySymbol) (tag : Tag) :
    afterLinkData data targetCount remainingTargets tag =
      { data with
        targets := remainingTargets
        scratch := []
        linkIndex := () :: data.linkIndex
        outputReverse :=
          (emittedLinkTokens data targetCount tag).reverse ++
            data.outputReverse } := by
  simp only [afterLinkData, afterIncrementLinkData]
  rw [afterFinishedSourceData_afterPrefix_eq]
  rw [afterFinishedTargetData_afterPrefix_eq]
  simp only [emittedLinkTokens, List.reverse_append,
    targetRecordTokens, targetCounterPrefix,
    targetCounterPrefixReverse, targetTargetIndexReverse,
    targetSourceFieldReverse, targetEdgeIndexFieldReverse,
    targetEdgeFieldReverse, targetVertexFieldReverse,
    copiedOutput, List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
