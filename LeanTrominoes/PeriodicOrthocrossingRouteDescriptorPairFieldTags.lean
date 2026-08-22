/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorBinaryWordData

/-! # Finite field tags for binary route-descriptor pairs -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

inductive Side
  | first
  | second
  deriving DecidableEq, Fintype

/-- Unary units tagged by descriptor side and one of the eleven field
positions, with explicit pair boundaries. -/
inductive Token
  | pairStart
  | unit (side : Side) (field : Fin 11)
  | pairEnd
  deriving DecidableEq, Fintype, Inhabited

inductive Control
  | between
  | first (field : Fin 11)
  | second (field : Fin 11)
  deriving DecidableEq, Fintype

def nextField (field : Fin 11) : Fin 11 :=
  ⟨(field.val + 1) % 11, Nat.mod_lt _ (by omega)⟩

def advanceFields : Fin 11 → Nat → Fin 11
  | field, 0 => field
  | field, count + 1 => advanceFields (nextField field) count

def sideControl : Side → Fin 11 → Control
  | .first, field => .first field
  | .second, field => .second field

def sideBit : Side → Bool → DelimitedBinaryWordPairs.Token
  | .first, bit => .firstBit bit
  | .second, bit => .secondBit bit

/-- Tagged units for a sequence of unary fields beginning at the supplied
field position. -/
def taggedFields : Side → Fin 11 → List Nat → List Token
  | _, _, [] => []
  | side, field, number :: numbers =>
      List.replicate number (.unit side field) ++
        taggedFields side (nextField field) numbers

/-- Tagged units of one canonical eleven-field descriptor. -/
def descriptorUnits (side : Side) (descriptor : RouteDescriptor) :
    List Token :=
  taggedFields side 0 descriptor.unaryFields

/-- Canonical tagged output block for one ordered descriptor pair. -/
def descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor) : List Token :=
  .pairStart ::
    (descriptorUnits .first pair.1 ++
      descriptorUnits .second pair.2 ++ [.pairEnd])

/-- Canonical tagged output for a descriptor-pair list. -/
def encodeDescriptorPairs
    (pairs : List (RouteDescriptor × RouteDescriptor)) : List Token :=
  pairs.flatMap descriptorPairTokens

/-- Tag units while a finite modulo-eleven counter follows the field
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

/-- Physical tagged-field output for an arbitrary pair-token stream. -/
def tokens (source : List DelimitedBinaryWordPairs.Token) : List Token :=
  FiniteStateTransducer.output .between transition finish source

/-- Tagged output presented at the semantic pair-list input boundary. -/
def inputTokens (input : DelimitedBinaryWordPairs.Input) : List Token :=
  tokens (DelimitedBinaryWordPairs.encode input)

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
