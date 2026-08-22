/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterSourceSemantics
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time source cycle-link route-emitter tokens -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter

open Computability Turing

/-- Preparing the tagged input and running the finite tagged emitter produces
the complete semantic cycle-link emitter stream in polynomial time. -/
noncomputable def emitterTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source
      (List UnaryProgramTokens.Token)
      PeriodicCNFFlatEncoding.Symbol UnaryProgramTokens.Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode id
      (fun source => emit (sourceInput source)) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceCycleLinkTaggedRouteEmitter.sourceInputComputableInPolyTime
    SourceCycleLinkTaggedRouteEmitterMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    fun source => by
      simpa only [id_eq] using
        SourceCycleLinkTaggedRouteEmitter.emit_sourceInput_eq_groupEmitter
          source

end LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter

end
