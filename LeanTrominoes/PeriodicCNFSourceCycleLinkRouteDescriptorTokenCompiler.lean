/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterSemanticOutput
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterTokenCompiler

/-! # Polynomial-time source cycle-link descriptor tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceCycleLinkRouteEmitter

open Computability Turing

/-- The certified cycle-link emitter computes the exact cycle-link suffix
route-descriptor token stream in polynomial time. -/
noncomputable def cycleLinkRouteDescriptorTokensComputableInPolyTime :
    @TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.Source
      (List UnaryProgramTokens.Token)
      PeriodicCNFFlatEncoding.Symbol UnaryProgramTokens.Token
      SourceSplitRouteDescriptorTokens.finEncoding.encode id
      (fun source =>
        PeriodicOrthocrossing.routeDescriptorTokens
          (PeriodicThreeSATThree.cycleLinkRouteDescriptors
            source.formula)) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    emitterTokensComputableInPolyTime fun source => by
      simpa only [id_eq] using
        emit_sourceInput_eq_cycleLinkRouteDescriptorTokens source

end SourceCycleLinkRouteEmitter
end PeriodicCNF
end LeanTrominoes

end
