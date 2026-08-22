/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterData

/-! # Linear output-length bound for one occurrence route -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

def routeSize (clauseCount literalCount clauseIndex edgeIndex targetIndex :
    Nat) : Nat :=
  clauseCount + literalCount + clauseIndex + edgeIndex + targetIndex + 1

theorem routeTokens_length_le (clauseCount literalCount clauseIndex
    edgeIndex : Nat) (literalIndex : Fin 3) (targetIndex : Nat)
    (literalNext anchorNext : Bool) :
    (routeTokens clauseCount literalCount clauseIndex edgeIndex
      literalIndex targetIndex literalNext anchorNext).length ≤
      15 * routeSize clauseCount literalCount clauseIndex edgeIndex
        targetIndex := by
  cases literalNext <;> cases anchorNext <;>
    simp [routeTokens, routeFields, offsetFields, routeSize,
      CountedUnaryFieldTokens.countedFieldBlock,
      CountedUnaryFieldTokens.fields, CountedUnaryFieldTokens.field,
      UnaryProgramTokens.atomTokens, SourceForwardOffset.relative,
      SourceForwardOffset.coordinate] <;>
    omega

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter
