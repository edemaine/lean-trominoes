/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotBinaryWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTags

/-! # Twelve-field tags for route-descriptor occurrence-slot pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotPairFieldTags

abbrev Side := RouteDescriptorPairFieldTags.Side

/-- Unary units tagged by pair side and one of twelve field positions.  The
first eleven positions are the descriptor fields and position eleven is the
fixed occurrence-slot index. -/
inductive Token
  | pairStart
  | unit (side : Side) (field : Fin 12)
  | pairEnd
  deriving DecidableEq, Fintype, Inhabited

inductive Control
  | between
  | first (field : Fin 12)
  | second (field : Fin 12)
  deriving DecidableEq, Fintype

def nextField (field : Fin 12) : Fin 12 :=
  ⟨(field.val + 1) % 12, Nat.mod_lt _ (by omega)⟩

def advanceFields : Fin 12 → Nat → Fin 12
  | field, 0 => field
  | field, count + 1 => advanceFields (nextField field) count

def sideControl : Side → Fin 12 → Control
  | .first, field => .first field
  | .second, field => .second field

def sideBit : Side → Bool → DelimitedBinaryWordPairs.Token
  | .first, bit => .firstBit bit
  | .second, bit => .secondBit bit

/-- Tagged units for a sequence of unary fields beginning at the supplied
field position. -/
def taggedFields : Side → Fin 12 → List Nat → List Token
  | _, _, [] => []
  | side, field, number :: numbers =>
      List.replicate number (.unit side field) ++
        taggedFields side (nextField field) numbers

/-- Eleven descriptor fields followed by the occurrence-slot field. -/
def descriptorSlotFields
    (tagged : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List Nat :=
  tagged.1.unaryFields ++ [tagged.2.val]

/-- Canonical tagged units for one descriptor occurrence slot. -/
def descriptorSlotUnits
    (side : Side)
    (tagged : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List Token :=
  taggedFields side 0 (descriptorSlotFields tagged)

/-- Canonical tagged output for one ordered descriptor-slot pair. -/
def descriptorSlotPairTokens
    (pair :
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
        RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor) :
    List Token :=
  .pairStart ::
    (descriptorSlotUnits .first pair.1 ++
      descriptorSlotUnits .second pair.2 ++ [.pairEnd])

/-- Canonical tagged output for a descriptor-slot pair list. -/
def encodeDescriptorSlotPairs
    (pairs : List
      (RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
        RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor)) :
    List Token :=
  pairs.flatMap descriptorSlotPairTokens

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

/-- Physical twelve-field tagged output for an arbitrary pair-token stream. -/
def tokens (source : List DelimitedBinaryWordPairs.Token) : List Token :=
  FiniteStateTransducer.output .between transition finish source

/-- Twelve-field tags at the semantic pair-list input boundary. -/
def inputTokens (input : DelimitedBinaryWordPairs.Input) : List Token :=
  tokens (DelimitedBinaryWordPairs.encode input)

/-- Forget slot-field units, converting the remaining stream to the existing
eleven-field descriptor-pair alphabet. -/
def descriptorProjection : Token → List RouteDescriptorPairFieldTags.Token
  | .pairStart => [.pairStart]
  | .pairEnd => [.pairEnd]
  | .unit side field =>
      if within : field.val < 11 then
        [.unit side ⟨field.val, within⟩]
      else
        []

/-- Project a complete twelve-field stream to its descriptor-only tags. -/
def descriptorTokens (source : List Token) :
    List RouteDescriptorPairFieldTags.Token :=
  source.flatMap descriptorProjection

end RouteDescriptorOccurrenceSlotPairFieldTags
end LeanTrominoes.PeriodicOrthocrossing
