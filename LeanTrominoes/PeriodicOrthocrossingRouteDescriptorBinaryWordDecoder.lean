/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokenDecoder

/-! # Decoder for individual binary route-descriptor words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWords

/-- Interpret a binary-word bit as one token of a delimiter-terminated unary
field stream. -/
def bitToken : Bool → RouteDescriptorScanTokens.Token
  | false => .unit
  | true => .fieldEnd

/-- Decode exactly eleven unary fields and reject any trailing bits. -/
def decodeWord (word : List Bool) : Option RouteDescriptor :=
  match RouteDescriptorScanTokens.takeFields 11 (word.map bitToken) with
  | some (fields, []) => RouteDescriptor.ofUnaryFields? fields
  | _ => none

/-- Decode both words of a pair, rejecting the pair if either word is not a
canonical complete descriptor record. -/
def decodePair
    (pair : List Bool × List Bool) :
    Option (RouteDescriptor × RouteDescriptor) := do
  let first ← decodeWord pair.1
  let second ← decodeWord pair.2
  pure (first, second)

end RouteDescriptorBinaryWords
end PeriodicOrthocrossing
end LeanTrominoes
