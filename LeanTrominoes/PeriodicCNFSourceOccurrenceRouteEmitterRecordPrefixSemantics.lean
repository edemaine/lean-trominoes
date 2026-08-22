/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterRecordFieldSemantics

/-! # Counter-prefix token semantics for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem recordCounterPrefix_eq (data : TapeData) :
    recordCounterPrefix data =
      .clauseMarker :: CountedUnaryFieldTokens.fields
        [data.clauseCount.length + 2 * data.literalCount.length,
          3 * data.literalCount.length,
          data.edgeIndex.length,
          data.literalCount.length + data.clauseIndex.length] := by
  simp only [recordCounterPrefix, recordCounterPrefixReverse,
    List.reverse_append, List.reverse_singleton,
    vertexFieldReverse_reverse, edgeFieldReverse_reverse,
    edgeIndexFieldReverse_reverse, sourceFieldReverse_reverse,
    CountedUnaryFieldTokens.fields, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.singleton_append]

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
