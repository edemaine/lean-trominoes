/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorScanTokens

/-! # Binary words for normalized route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorBinaryWords

open RouteDescriptorScanTokens

/-- Unary data for one descriptor field, terminated by a `true` bit. -/
def fieldWord (number : Nat) : List Bool :=
  List.replicate number false ++ [true]

/-- The eleven unary fields of one descriptor, concatenated into one word. -/
def descriptorWord (descriptor : RouteDescriptor) : List Bool :=
  descriptor.unaryFields.flatMap fieldWord

/-- Semantic binary-word representation of a descriptor list. -/
def words (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  ⟨descriptors.map descriptorWord⟩

/-- The finite control records how many field delimiters have been seen in
the current eleven-field descriptor. -/
abbrev Control := Fin 11

/-- Advance the field counter, wrapping after the eleventh field. -/
def nextControl (control : Control) : Control :=
  ⟨(control.val + 1) % 11, Nat.mod_lt _ (by omega)⟩

/-- Convert normalized descriptor tokens to delimited binary-word tokens.
The eleventh field delimiter also closes the current word. -/
def transition : Control → RouteDescriptorScanTokens.Token →
    Control × List DelimitedBinaryWords.Token
  | _, .recordStart => (0, [.wordStart])
  | control, .unit => (control, [.bit false])
  | control, .fieldEnd =>
      (nextControl control,
        if control.val = 10 then [.bit true, .wordEnd]
        else [.bit true])

/-- Canonical records are already closed by their eleventh field. -/
def finish (_ : Control) : List DelimitedBinaryWords.Token := []

/-- Physical output of the fixed eleven-state encoder. -/
def tokens (source : List RouteDescriptorScanTokens.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output 0 transition finish source

end RouteDescriptorBinaryWords
end PeriodicOrthocrossing
end LeanTrominoes
