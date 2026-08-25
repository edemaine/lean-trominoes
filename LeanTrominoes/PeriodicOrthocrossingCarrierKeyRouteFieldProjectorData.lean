/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Finite-state projection of guarded carrier-key route fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRouteFieldProjector

inductive Control
  | outside
  | guard
  | route
  | skip
  | inactive
  deriving DecidableEq, Fintype

def transition : Control → DelimitedBinaryWords.Token →
    Control × List UnaryFieldEncoderMachine.Symbol
  | .outside, .wordStart => (.guard, [])
  | .guard, .bit true => (.route, [])
  | .guard, .bit false => (.inactive, [])
  | .route, .bit false => (.route, [.unit])
  | .route, .bit true => (.skip, [.delimiter])
  | .skip, .bit _ => (.skip, [])
  | .skip, .wordEnd => (.outside, [])
  | .inactive, .wordEnd => (.outside, [.delimiter])
  | .inactive, .bit _ => (.inactive, [])
  | _, _ => (.outside, [])

/-- Always append the unary-zero sentinel required by representative
lookup. -/
def finish (_ : Control) : List UnaryFieldEncoderMachine.Symbol :=
  [.delimiter]

def output (tokens : List DelimitedBinaryWords.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  FiniteStateTransducer.output .outside transition finish tokens

end CarrierKeyRouteFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
