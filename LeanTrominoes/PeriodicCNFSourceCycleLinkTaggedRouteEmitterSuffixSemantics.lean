/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceFieldSemantics

/-! # Tag-dependent suffix token semantics -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem sourceSuffix_eq_fields (tag : Tag) :
    sourceSuffix tag = CountedUnaryFieldTokens.fields
      [0, SourceCycleLinkPositionTags.sourceTargetPortRank tag,
        0, 0, 0, 0] := by
  cases tag <;>
    simp [sourceSuffix, SourceCycleLinkPositionTags.sourceTargetPortRank,
      CountedUnaryFieldTokens.fields, CountedUnaryFieldTokens.field,
      PeriodicCNF.UnaryProgramTokens.atomTokens]

theorem targetSuffix_eq_fields (tag : Tag) :
    targetSuffix tag = CountedUnaryFieldTokens.fields
      [1, SourceCycleLinkPositionTags.targetTargetPortRank tag,
        0, 0, 0, 0] := by
  cases tag <;>
    simp [targetSuffix, SourceCycleLinkPositionTags.targetTargetPortRank,
      CountedUnaryFieldTokens.fields, CountedUnaryFieldTokens.field,
      PeriodicCNF.UnaryProgramTokens.atomTokens]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
