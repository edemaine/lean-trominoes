/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceRecordOutputSemantics
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetFieldSemantics
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetOutputData

/-! # Exact target-record output semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def targetRecordTokens (data : TapeData) (tag : Tag) : List OutputToken :=
  (targetCounterPrefix data ++ [.atomEnd]) ++ targetSuffix tag

theorem targetRecordTokens_eq_countedFieldBlock (data : TapeData)
    (tag : Tag) :
    targetRecordTokens data tag =
      CountedUnaryFieldTokens.countedFieldBlock
        [data.clauseCount.length + 2 * data.literalCount.length,
          3 * data.literalCount.length,
          data.literalCount.length + 2 * data.linkIndex.length + 1,
          data.literalCount.length + data.clauseCount.length +
            data.linkIndex.length,
          data.linkIndex.length, 1,
          SourceCycleLinkPositionTags.targetTargetPortRank tag,
          0, 0, 0, 0] := by
  rw [targetRecordTokens,
    targetCounterPrefix_append_end_eq, targetSuffix_eq_fields]
  simp [CountedUnaryFieldTokens.countedFieldBlock,
    CountedUnaryFieldTokens.fields, List.append_assoc]

theorem afterFinishedTargetData_afterPrefix_eq (data : TapeData)
    (tag : Tag) :
    afterFinishedTargetData (afterTargetPrefixData data) tag =
      { data with
        scratch := []
        outputReverse :=
          (targetRecordTokens data tag).reverse ++ data.outputReverse } := by
  rw [afterTargetPrefixData_eq]
  simp only [afterFinishedTargetData, targetRecordTokens,
    targetCounterPrefix, List.reverse_append, List.reverse_reverse,
    List.reverse_cons, List.nil_append,
    List.cons_append, List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
