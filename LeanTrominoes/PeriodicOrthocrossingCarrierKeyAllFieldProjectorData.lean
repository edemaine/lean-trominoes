/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData

/-! # Streaming every unary field of a guarded carrier key -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAllFieldProjector

inductive NatPart
  | route
  | segment
  deriving DecidableEq, Fintype

inductive Coordinate
  | horizontal
  | vertical
  deriving DecidableEq, Fintype

inductive Control
  | outside
  | guard
  | nat (part : NatPart)
  | intSign (coordinate : Coordinate)
  | intBody (coordinate : Coordinate) (negative : Bool)
  | skip
  | inactive
  deriving DecidableEq, Fintype

def nextCoordinate : Coordinate → Control
  | .horizontal => .intSign .vertical
  | .vertical => .skip

/-- Emit route, segment, negative horizontal magnitude, positive horizontal
magnitude, negative vertical magnitude, and positive vertical magnitude.  The
negative field precedes the positive field so signed words can later be
reconstructed without buffering an unbounded positive magnitude. -/
def transition : Control → DelimitedBinaryWords.Token →
    Control × List UnaryFieldEncoderMachine.Symbol
  | .outside, .wordStart => (.guard, [])
  | .guard, .bit true => (.nat .route, [])
  | .guard, .bit false => (.inactive, [])
  | .nat .route, .bit false => (.nat .route, [.unit])
  | .nat .route, .bit true => (.nat .segment, [.delimiter])
  | .nat .segment, .bit false => (.nat .segment, [.unit])
  | .nat .segment, .bit true => (.intSign .horizontal, [.delimiter])
  | .intSign coordinate, .bit true =>
      (.intBody coordinate true, [.unit])
  | .intSign coordinate, .bit false =>
      (.intBody coordinate false, [.delimiter])
  | .intBody coordinate negative, .bit false =>
      (.intBody coordinate negative, [.unit])
  | .intBody coordinate true, .bit true =>
      (nextCoordinate coordinate, [.delimiter, .delimiter])
  | .intBody coordinate false, .bit true =>
      (nextCoordinate coordinate, [.delimiter])
  | .skip, .wordEnd => (.outside, [])
  | .inactive, .wordEnd =>
      (.outside, List.replicate 6 .delimiter)
  | .skip, _ => (.skip, [])
  | .inactive, _ => (.inactive, [])
  | _, _ => (.outside, [])

/-- One rejected source-pair sentinel contributes twelve zero fields. -/
def finish (_ : Control) : List UnaryFieldEncoderMachine.Symbol :=
  List.replicate 12 .delimiter

def keyFields : Option CarrierKeyWords.CarrierKey → List Nat
  | none => List.replicate 6 0
  | some key =>
      [key.1, key.2.1,
        (-key.2.2.1).toNat, key.2.2.1.toNat,
        (-key.2.2.2).toNat, key.2.2.2.toNat]

def valuesWithSentinel
    (keys : List (Option CarrierKeyWords.CarrierKey)) : List Nat :=
  keys.flatMap keyFields ++ List.replicate 12 0

def output (tokens : List DelimitedBinaryWords.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  FiniteStateTransducer.output .outside transition finish tokens

end CarrierKeyAllFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
