/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorData

/-! # Physical pipeline for the carrier boundary-presence field -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresencePipeline

def terminalFields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  GuardedPresenceFieldProjector.output false
    (CarrierActiveKeyRecipeStream.terminalTokens input)

def crossingFields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  GuardedPresenceFieldProjector.output true
    (CarrierActiveKeyRecipeStream.crossingTokens input)

def fields (input : DelimitedBinaryWords.Input) :
    List UnaryFieldEncoderMachine.Symbol :=
  terminalFields input ++ crossingFields input ++
    [UnaryFieldEncoderMachine.Symbol.delimiter]

end CarrierBoundaryPresencePipeline
end LeanTrominoes.PeriodicOrthocrossing
