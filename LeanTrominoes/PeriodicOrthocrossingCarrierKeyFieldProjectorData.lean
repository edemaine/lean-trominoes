/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Finite-state projection of all guarded carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

/-- The six unary columns of a physical carrier key. -/
inductive Field
  | route
  | segment
  | horizontalPositive
  | horizontalNegative
  | verticalPositive
  | verticalNegative
  deriving DecidableEq, Fintype

inductive NatPart
  | route
  | segment
  deriving DecidableEq, Fintype

inductive Coordinate
  | horizontal
  | vertical
  deriving DecidableEq, Fintype

inductive IntMode
  | skip
  | zero
  | units
  deriving DecidableEq, Fintype

inductive Control
  | outside
  | guard
  | nat (part : NatPart)
  | intSign (coordinate : Coordinate)
  | intBody (coordinate : Coordinate) (mode : IntMode)
  | skip
  | inactive
  deriving DecidableEq, Fintype

def selectsNat : Field → NatPart → Bool
  | .route, .route => true
  | .segment, .segment => true
  | _, _ => false

def selectsSigned : Field → Coordinate → Bool → Bool
  | .horizontalPositive, .horizontal, false => true
  | .horizontalNegative, .horizontal, true => true
  | .verticalPositive, .vertical, false => true
  | .verticalNegative, .vertical, true => true
  | _, _, _ => false

def selectsCoordinate : Field → Coordinate → Bool
  | .horizontalPositive, .horizontal => true
  | .horizontalNegative, .horizontal => true
  | .verticalPositive, .vertical => true
  | .verticalNegative, .vertical => true
  | _, _ => false

def intMode (field : Field) (coordinate : Coordinate)
    (sign : Bool) : IntMode :=
  if selectsSigned field coordinate sign then
    .units
  else if selectsCoordinate field coordinate then
    .zero
  else
    .skip

def transition (field : Field) : Control → DelimitedBinaryWords.Token →
    Control × List UnaryFieldEncoderMachine.Symbol
  | .outside, .wordStart => (.guard, [])
  | .guard, .bit true => (.nat .route, [])
  | .guard, .bit false => (.inactive, [])
  | .nat part, .bit false =>
      (.nat part, if selectsNat field part then [.unit] else [])
  | .nat .route, .bit true =>
      if selectsNat field .route then
        (.skip, [.delimiter])
      else
        (.nat .segment, [])
  | .nat .segment, .bit true =>
      if selectsNat field .segment then
        (.skip, [.delimiter])
      else
        (.intSign .horizontal, [])
  | .intSign coordinate, .bit sign =>
      match intMode field coordinate sign with
      | .units =>
          (.intBody coordinate .units, if sign then [.unit] else [])
      | .zero => (.intBody coordinate .zero, [])
      | .skip => (.intBody coordinate .skip, [])
  | .intBody coordinate .units, .bit false =>
      (.intBody coordinate .units, [.unit])
  | .intBody coordinate .zero, .bit false =>
      (.intBody coordinate .zero, [])
  | .intBody coordinate .skip, .bit false =>
      (.intBody coordinate .skip, [])
  | .intBody .horizontal .skip, .bit true =>
      (.intSign .vertical, [])
  | .intBody .horizontal .zero, .bit true =>
      (.skip, [.delimiter])
  | .intBody .horizontal .units, .bit true =>
      (.skip, [.delimiter])
  | .intBody .vertical .skip, .bit true =>
      (.skip, [])
  | .intBody .vertical .zero, .bit true =>
      (.skip, [.delimiter])
  | .intBody .vertical .units, .bit true =>
      (.skip, [.delimiter])
  | .skip, .bit _ => (.skip, [])
  | .skip, .wordEnd => (.outside, [])
  | .inactive, .bit _ => (.inactive, [])
  | .inactive, .wordEnd => (.outside, [.delimiter])
  | _, _ => (.outside, [])

/-- Always append the unary-zero sentinel required by representative
lookup. -/
def finish (_ : Control) : List UnaryFieldEncoderMachine.Symbol :=
  [.delimiter]

def keyValue : Field → CarrierKeyWords.CarrierKey → Nat
  | .route, key => key.1
  | .segment, key => key.2.1
  | .horizontalPositive, key => key.2.2.1.toNat
  | .horizontalNegative, key => (-key.2.2.1).toNat
  | .verticalPositive, key => key.2.2.2.toNat
  | .verticalNegative, key => (-key.2.2.2).toNat

def value (field : Field) : Option CarrierKeyWords.CarrierKey → Nat
  | none => 0
  | some key => keyValue field key

def semanticWord : Option CarrierKeyWords.CarrierKey → List Bool
  | none => [false]
  | some key => true :: CarrierKeyWords.word key

def output (field : Field) (tokens : List DelimitedBinaryWords.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  FiniteStateTransducer.output .outside (transition field) finish tokens

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
