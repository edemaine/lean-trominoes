/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryColumnCompiler
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionBatchCompiler

/-! # Compiling aligned normalized fallback-suffix query columns -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixQueryColumns

open Computability Turing
open FallbackSuffixDirectionCompiler
open FallbackSuffixQueryFormatter

/-- Exact aligned finite-role, unary-radial, and finite-slot producers can
be interpreted as normalized route-delimited suffix directions. -/
noncomputable def normalizedDirectionsComputableInPolyTimeOf
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (roles : Input → List HeaderRole)
    (radials : Input → List Nat)
    (slots : Input → List RetainedTerminalSlot)
    (rolesSlotsLength : ∀ input,
      (roles input).length = (slots input).length)
    (rolesRadialsLength : ∀ input,
      (roles input).length = (radials input).length)
    (rolesCompiler :
      @TM2ComputableInPolyTime
        Input (List HeaderRole) InputSymbol HeaderRole
        encodeInput id roles)
    (radialsCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields radials)
    (slotsCompiler :
      @TM2ComputableInPolyTime
        Input (List RetainedTerminalSlot) InputSymbol RetainedTerminalSlot
        encodeInput id slots) :
    @TM2ComputableInPolyTime
      Input (List OutputToken)
        InputSymbol OutputToken
      encodeInput id
      (fun input =>
        NormalizedFallbackSuffixDirectionCompiler.Batch.directions
          (alignedQueries (roles input) (radials input) (slots input))) :=
  TM2CompositionMachine.computableInPolyTime
    (encodeComputableInPolyTimeOf encodeInput roles radials slots
      rolesSlotsLength rolesRadialsLength
      rolesCompiler radialsCompiler slotsCompiler)
    NormalizedFallbackSuffixDirectionCompiler.Batch.directionsComputableInPolyTime

end FallbackSuffixQueryColumns
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
