/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokens

/-! # Decoder for normalized route-descriptor scan tokens -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorScanTokens

/-- Consume one delimiter-terminated unary field. -/
def takeField : List Token → Option (Nat × List Token)
  | .unit :: tokens => do
      let result ← takeField tokens
      pure (result.1 + 1, result.2)
  | .fieldEnd :: tokens => some (0, tokens)
  | _ => none

/-- Consume exactly `count` unary fields. -/
def takeFields : Nat → List Token → Option (List Nat × List Token)
  | 0, tokens => some ([], tokens)
  | count + 1, tokens => do
      let first ← takeField tokens
      let remaining ← takeFields count first.2
      pure (first.1 :: remaining.1, remaining.2)

/-- Fuel-bounded record decoder.  One fuel unit is consumed per record; the
public decoder supplies the larger physical-token length. -/
def decodeAux : Nat → List Token → Option (List RouteDescriptor)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, .recordStart :: tokens => do
      let fields ← takeFields 11 tokens
      let descriptor ← RouteDescriptor.ofUnaryFields? fields.1
      let remaining ← decodeAux fuel fields.2
      pure (descriptor :: remaining)
  | _, _ => none

/-- Total decoder for normalized route-descriptor records. -/
def decode (tokens : List Token) : Option (List RouteDescriptor) :=
  decodeAux (tokens.length + 1) tokens

end RouteDescriptorScanTokens
end PeriodicOrthocrossing
end LeanTrominoes
