/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceOutputData

/-! # Source-record counter-field token semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem copiedOutput_eq_atomTokens (counter : List Unit) :
    copiedOutput counter =
      PeriodicCNF.UnaryProgramTokens.atomTokens counter.length := by
  simp [copiedOutput, PeriodicCNF.UnaryProgramTokens.atomTokens]

theorem sourceVertexFieldReverse_reverse (data : TapeData) :
    (sourceVertexFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.clauseCount.length + 2 * data.literalCount.length) := by
  simp only [sourceVertexFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem sourceEdgeFieldReverse_reverse (data : TapeData) :
    (sourceEdgeFieldReverse data).reverse =
      CountedUnaryFieldTokens.field (3 * data.literalCount.length) := by
  simp only [sourceEdgeFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem sourceEdgeIndexFieldReverse_reverse (data : TapeData) :
    (sourceEdgeIndexFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.literalCount.length + 2 * data.linkIndex.length) := by
  simp only [sourceEdgeIndexFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem sourceSourceFieldReverse_reverse (data : TapeData) :
    (sourceSourceFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.literalCount.length + data.clauseCount.length +
          data.linkIndex.length) := by
  simp only [sourceSourceFieldReverse, List.reverse_cons,
    List.reverse_append, copiedOutput_eq_atomTokens,
    List.reverse_replicate, CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    List.append_assoc]

theorem sourceCounterPrefix_eq (data : TapeData) :
    sourceCounterPrefix data =
      .clauseMarker :: CountedUnaryFieldTokens.fields
        [data.clauseCount.length + 2 * data.literalCount.length,
          3 * data.literalCount.length,
          data.literalCount.length + 2 * data.linkIndex.length,
          data.literalCount.length + data.clauseCount.length +
            data.linkIndex.length] := by
  simp only [sourceCounterPrefix, sourceCounterPrefixReverse,
    List.reverse_append, List.reverse_singleton,
    sourceVertexFieldReverse_reverse, sourceEdgeFieldReverse_reverse,
    sourceEdgeIndexFieldReverse_reverse,
    sourceSourceFieldReverse_reverse,
    CountedUnaryFieldTokens.fields, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.singleton_append]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
