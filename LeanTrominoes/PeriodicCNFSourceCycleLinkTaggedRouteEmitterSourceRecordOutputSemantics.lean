/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceOutputData
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSuffixSemantics

/-! # Exact source-record output semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem countedField_reverse (number : Nat) :
    (CountedUnaryFieldTokens.field number).reverse =
      .atomEnd :: List.replicate number (.atomUnit : OutputToken) := by
  simp [CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens]

def sourceRecordTokens (data : TapeData) (targetCount : Nat)
    (tag : Tag) : List OutputToken :=
  sourceCounterPrefix data ++
    CountedUnaryFieldTokens.field targetCount ++ sourceSuffix tag

theorem sourceRecordTokens_eq_countedFieldBlock (data : TapeData)
    (targetCount : Nat) (tag : Tag) :
    sourceRecordTokens data targetCount tag =
      CountedUnaryFieldTokens.countedFieldBlock
        [data.clauseCount.length + 2 * data.literalCount.length,
          3 * data.literalCount.length,
          data.literalCount.length + 2 * data.linkIndex.length,
          data.literalCount.length + data.clauseCount.length +
            data.linkIndex.length,
          targetCount, 0,
          SourceCycleLinkPositionTags.sourceTargetPortRank tag,
          0, 0, 0, 0] := by
  rw [sourceRecordTokens, sourceCounterPrefix_eq,
    sourceSuffix_eq_fields]
  simp [CountedUnaryFieldTokens.countedFieldBlock,
    CountedUnaryFieldTokens.fields, List.append_assoc]

theorem afterFinishedSourceData_afterPrefix_eq (data : TapeData)
    (targetCount : Nat) (remainingTargets : List UnarySymbol)
    (tag : Tag) :
    afterFinishedSourceData (afterSourcePrefixData data)
        targetCount remainingTargets tag =
      { data with
        scratch := []
        targets := remainingTargets
        outputReverse :=
          (sourceRecordTokens data targetCount tag).reverse ++
            data.outputReverse } := by
  rw [afterSourcePrefixData_eq]
  simp only [afterFinishedSourceData, afterSourceTargetData,
    sourceRecordTokens, sourceCounterPrefix, List.reverse_append,
    List.reverse_reverse, countedField_reverse, List.cons_append,
    List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
