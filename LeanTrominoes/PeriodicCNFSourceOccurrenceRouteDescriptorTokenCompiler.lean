/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterSemanticOutput
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time source occurrence-route descriptor tokens -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

open Computability Turing

/-- The certified input preparation and route emitter compose to produce the
complete occurrence-prefix descriptor token stream in polynomial time. -/
noncomputable def occurrenceRouteDescriptorTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source
      (List UnaryProgramTokens.Token)
      PeriodicCNFFlatEncoding.Symbol UnaryProgramTokens.Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode id
      (fun source =>
        PeriodicOrthocrossing.routeDescriptorTokens
          (PeriodicThreeSATThree.occurrenceRouteDescriptors
            source.formula)) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    sourceInputComputableInPolyTime
    SourceOccurrenceRouteEmitterMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    fun source => by
      simpa only [id_eq] using emit_sourceInput source

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitter

end
