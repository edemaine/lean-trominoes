/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokens

/-! # Compact source-terminal words from route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorSourceTerminalCompactWords

open RouteDescriptorScanTokens

/-- Compact retained-atom word of a route's normalized source terminal. -/
def word (descriptor : RouteDescriptor) : List Bool :=
  [false, false] ++ CarrierKeyWords.word
    (descriptor.edgeIndex, 0, (0, 0))

def words (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨descriptors.map word⟩

/-- Current field of the fixed eleven-field descriptor record. -/
abbrev Control := Fin 11

def nextControl (control : Control) : Control :=
  ⟨(control.val + 1) % 11, Nat.mod_lt _ (by omega)⟩

/-- Retain field two (`edgeIndex`) and wrap it with the terminal constructor,
zero segment index, and zero occurrence translate. -/
def transition : Control → RouteDescriptorScanTokens.Token →
    Control × List DelimitedBinaryWords.Token
  | _, .recordStart =>
      (0, [.wordStart, .bit false, .bit false])
  | control, .unit =>
      (control, if control.val = 2 then [.bit false] else [])
  | control, .fieldEnd =>
      (nextControl control,
        if control.val = 2 then
          [.bit true, .bit true,
            .bit false, .bit true, .bit false, .bit true,
            .wordEnd]
        else [])

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

def tokens (source : List RouteDescriptorScanTokens.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output 0 transition finish source

end RouteDescriptorSourceTerminalCompactWords
end PeriodicOrthocrossing
end LeanTrominoes
