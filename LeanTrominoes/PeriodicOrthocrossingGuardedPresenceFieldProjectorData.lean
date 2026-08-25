/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Guarded-word projection to constant presence fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedPresenceFieldProjector

inductive Control
  | outside
  | guard
  | skip
  deriving DecidableEq, Fintype

/-- If `activeValue` is true, an active guarded word contributes unary one;
otherwise every word contributes unary zero. -/
def transition (activeValue : Bool) : Control →
    DelimitedBinaryWords.Token →
    Control × List UnaryFieldEncoderMachine.Symbol
  | .outside, .wordStart => (.guard, [])
  | .guard, .bit false => (.skip, [.delimiter])
  | .guard, .bit true =>
      (.skip, if activeValue then [.unit, .delimiter] else [.delimiter])
  | .skip, .bit _ => (.skip, [])
  | .skip, .wordEnd => (.outside, [])
  | _, _ => (.outside, [])

/-- Partial streams contribute no sentinel; callers append one after joining
all source-kind streams. -/
def finish (_ : Control) : List UnaryFieldEncoderMachine.Symbol :=
  []

def value (activeValue : Bool) :
    Option CarrierKeyWords.CarrierKey → Nat
  | none => 0
  | some _ => if activeValue then 1 else 0

def semanticWord : Option CarrierKeyWords.CarrierKey → List Bool
  | none => [false]
  | some key => true :: CarrierKeyWords.word key

def output (activeValue : Bool)
    (tokens : List DelimitedBinaryWords.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  FiniteStateTransducer.output .outside
    (transition activeValue) finish tokens

end GuardedPresenceFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
