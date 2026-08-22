/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceFieldSemantics
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTargetOutputData

/-! # Target-record counter-field token semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem targetVertexFieldReverse_reverse (data : TapeData) :
    (targetVertexFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.clauseCount.length + 2 * data.literalCount.length) := by
  simp only [targetVertexFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem targetEdgeFieldReverse_reverse (data : TapeData) :
    (targetEdgeFieldReverse data).reverse =
      CountedUnaryFieldTokens.field (3 * data.literalCount.length) := by
  simp only [targetEdgeFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem targetEdgeIndexFieldReverse_reverse (data : TapeData) :
    (targetEdgeIndexFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.literalCount.length + 2 * data.linkIndex.length + 1) := by
  simp only [targetEdgeIndexFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc, List.singleton_append, List.replicate_one]

theorem targetSourceFieldReverse_reverse (data : TapeData) :
    (targetSourceFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.literalCount.length + data.clauseCount.length +
          data.linkIndex.length) := by
  simp only [targetSourceFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    List.append_assoc]

theorem targetTargetIndexReverse_reverse_append_end (data : TapeData) :
    (targetTargetIndexReverse data).reverse ++ [.atomEnd] =
      CountedUnaryFieldTokens.field data.linkIndex.length := by
  simp [targetTargetIndexReverse, copiedOutput_eq_atomTokens,
    CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens]

theorem targetCounterPrefix_append_end_eq (data : TapeData) :
    targetCounterPrefix data ++ [.atomEnd] =
      .clauseMarker :: CountedUnaryFieldTokens.fields
        [data.clauseCount.length + 2 * data.literalCount.length,
          3 * data.literalCount.length,
          data.literalCount.length + 2 * data.linkIndex.length + 1,
          data.literalCount.length + data.clauseCount.length +
            data.linkIndex.length,
          data.linkIndex.length] := by
  simp only [targetCounterPrefix, targetCounterPrefixReverse,
    List.reverse_append, List.reverse_singleton,
    targetVertexFieldReverse_reverse, targetEdgeFieldReverse_reverse,
    targetEdgeIndexFieldReverse_reverse,
    targetSourceFieldReverse_reverse, CountedUnaryFieldTokens.fields,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.singleton_append, List.append_assoc]
  rw [targetTargetIndexReverse_reverse_append_end]
  simp only [List.cons_append]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
