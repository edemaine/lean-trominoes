/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Physical compiler for generic active carrier-key fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierActiveKeyFieldProjection

open Computability Turing

/-- Emit one fixed physical unary key column from an encoded descriptor-word
stream. -/
noncomputable def physicalOutputComputableInPolyTime
    (field : CarrierKeyFieldProjector.Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      (fun input => CarrierKeyFieldProjector.output field
        (CarrierActiveKeyRecipeStream.emittedTokens input)) :=
  TM2CompositionMachine.computableInPolyTime
    CarrierActiveKeyRecipeStream.emittedTokensComputableInPolyTime
    (CarrierKeyFieldProjector.computableInPolyTime field)

end CarrierActiveKeyFieldProjection
end LeanTrominoes.PeriodicOrthocrossing

end
