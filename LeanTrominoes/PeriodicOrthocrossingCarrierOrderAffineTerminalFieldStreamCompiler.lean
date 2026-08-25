/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Pair-stream compiler for terminal order-coordinate fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalDirectionalOrderFieldStream

open Computability Turing

def blockFields (keepPositive : Bool)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (RouteDescriptorPairAffine.terminalDirectionalOrderFields
      keepPositive tokens)

def blockFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime id id (blockFields keepPositive) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (RouteDescriptorPairAffine.terminalDirectionalOrderFieldsComputableInPolyTime
      keepPositive)
    (fun _ => rfl)

def emittedFields (keepPositive : Bool)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    (blockFields keepPositive) tokens

def emittedFieldsComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime id id (emittedFields keepPositive) :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (blockFieldsComputableInPolyTime keepPositive)
    RouteDescriptorPairFieldTags.isPairEnd

end TerminalDirectionalOrderFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
