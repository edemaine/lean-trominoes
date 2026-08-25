/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRouteFieldProjectorCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Physical compiler for active carrier-key route projection -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierActiveKeyRouteFieldProjection

open Computability Turing

/-- Emit the physical unary route fields from an encoded descriptor-word
stream. -/
noncomputable def physicalOutputComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (fun input => CarrierKeyRouteFieldProjector.output
        (CarrierActiveKeyRecipeStream.emittedTokens input)) :=
  TM2CompositionMachine.computableInPolyTime
    CarrierActiveKeyRecipeStream.emittedTokensComputableInPolyTime
    CarrierKeyRouteFieldProjector.computableInPolyTime

end CarrierActiveKeyRouteFieldProjection
end LeanTrominoes.PeriodicOrthocrossing

end
