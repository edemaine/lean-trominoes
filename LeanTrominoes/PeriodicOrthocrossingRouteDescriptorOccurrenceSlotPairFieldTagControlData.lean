/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagAlphabetData

/-! # Finite controls for occurrence-slot pair tags -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

deriving instance Fintype for RouteDescriptorPairFieldTags.Side
deriving instance Fintype for Token

inductive Control
  | between
  | first (field : Fin 12)
  | second (field : Fin 12)
  deriving DecidableEq, Fintype

def sideControl : Side → Fin 12 → Control
  | .first, field => .first field
  | .second, field => .second field

def sideBit : Side → Bool → DelimitedBinaryWordPairs.Token
  | .first, bit => .firstBit bit
  | .second, bit => .secondBit bit

/-- Tag units while a finite modulo-twelve counter follows the field
delimiters on each side of a pair. -/
def transition : Control → DelimitedBinaryWordPairs.Token →
    Control × List Token
  | _, .pairStart => (.first 0, [.pairStart])
  | .first field, .firstBit false =>
      (.first field, [.unit .first field])
  | .first field, .firstBit true =>
      (.first (nextField field), [])
  | _, .middle => (.second 0, [])
  | .second field, .secondBit false =>
      (.second field, [.unit .second field])
  | .second field, .secondBit true =>
      (.second (nextField field), [])
  | _, .pairEnd => (.between, [.pairEnd])
  | control, _ => (control, [])

def finish (_ : Control) : List Token := []

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
