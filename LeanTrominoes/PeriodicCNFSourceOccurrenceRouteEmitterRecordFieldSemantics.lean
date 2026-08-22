/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordOutputData

/-! # Counter-field token semantics for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem copiedOutput_eq_atomTokens (counter : List Unit) :
    copiedOutput counter =
      PeriodicCNF.UnaryProgramTokens.atomTokens counter.length := by
  simp [copiedOutput, PeriodicCNF.UnaryProgramTokens.atomTokens]

theorem vertexFieldReverse_reverse (data : TapeData) :
    (vertexFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.clauseCount.length + 2 * data.literalCount.length) := by
  simp only [vertexFieldReverse, List.reverse_cons, List.reverse_append,
    copiedOutput_eq_atomTokens, List.reverse_replicate,
    CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem edgeFieldReverse_reverse (data : TapeData) :
    (edgeFieldReverse data).reverse =
      CountedUnaryFieldTokens.field (3 * data.literalCount.length) := by
  simp only [edgeFieldReverse, List.reverse_cons, List.reverse_append,
    copiedOutput_eq_atomTokens, List.reverse_replicate,
    CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    Nat.succ_mul, Nat.zero_mul, List.replicate_zero, List.nil_append,
    List.append_assoc]

theorem edgeIndexFieldReverse_reverse (data : TapeData) :
    (edgeIndexFieldReverse data).reverse =
      CountedUnaryFieldTokens.field data.edgeIndex.length := by
  simp only [edgeIndexFieldReverse, List.reverse_cons,
    copiedOutput_eq_atomTokens, List.reverse_replicate,
    CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens]

theorem sourceFieldReverse_reverse (data : TapeData) :
    (sourceFieldReverse data).reverse =
      CountedUnaryFieldTokens.field
        (data.literalCount.length + data.clauseIndex.length) := by
  simp only [sourceFieldReverse, List.reverse_cons, List.reverse_append,
    copiedOutput_eq_atomTokens, List.reverse_replicate,
    CountedUnaryFieldTokens.field,
    PeriodicCNF.UnaryProgramTokens.atomTokens, List.replicate_add,
    List.append_assoc]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
