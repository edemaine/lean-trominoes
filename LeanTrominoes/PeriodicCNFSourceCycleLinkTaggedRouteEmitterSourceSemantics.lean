/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterInputCompiler
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputCompiler
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSemantics

/-! # Source semantics of tagged cycle-link emitter inputs -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitter

theorem sourceInput_eq_ofGroupInput
    (source : SourceSplitRouteDescriptorTokens.Source) :
    sourceInput source =
      ofGroupInput (SourceCycleLinkRouteEmitter.sourceInput source) := by
  unfold sourceInput ofGroupInput
  congr 1 <;>
    exact congrArg _
      (SourceCycleLinkRouteEmitter.compiledGroupSizes_eq_sourceInput source)

theorem emit_sourceInput_eq_groupEmitter
    (source : SourceSplitRouteDescriptorTokens.Source) :
    emit (sourceInput source) =
      SourceCycleLinkRouteEmitter.emit
        (SourceCycleLinkRouteEmitter.sourceInput source) := by
  rw [sourceInput_eq_ofGroupInput, emit_ofGroupInput]

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitter
