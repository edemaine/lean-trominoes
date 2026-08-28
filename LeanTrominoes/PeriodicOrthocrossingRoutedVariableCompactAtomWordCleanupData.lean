/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData

/-! # Alternating cleanup of routed-variable compact atom words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordCleanup

inductive Kind
  | terminal
  | sourceAtom
  deriving DecidableEq, Fintype, Inhabited

def Kind.next : Kind → Kind
  | .terminal => .sourceAtom
  | .sourceAtom => .terminal

/-- Retain the first terminated unary field of a carrier-key payload. -/
def firstNatField : List Bool → List Bool
  | [] => []
  | false :: bits => false :: firstNatField bits
  | true :: _ => [true]

/-- Interpret one active guarded key word according to its alternating slot.
False-headed sentinels and empty malformed words contribute no output. -/
def word : Kind → List Bool → List (List Bool)
  | .terminal, true :: key => [[false, false] ++ key]
  | .sourceAtom, true :: key =>
      [[true, false, false] ++ firstNatField key]
  | _, _ => []

def wordsFrom : Kind → List (List Bool) → List (List Bool)
  | _, [] => []
  | kind, guarded :: rest =>
      word kind guarded ++ wordsFrom kind.next rest

def words (guarded : List (List Bool)) : List (List Bool) :=
  wordsFrom .terminal guarded

def compact (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨words input.words⟩

inductive Control
  | between (kind : Kind)
  | guard (kind : Kind)
  | terminalBody
  | sourceAtomRoute
  | sourceAtomSkip
  | discard (kind : Kind)
  deriving DecidableEq, Fintype, Inhabited

def transition : Control → DelimitedBinaryWords.Token →
    Control × List DelimitedBinaryWords.Token
  | .between kind, .wordStart => (.guard kind, [])
  | .guard .terminal, .bit true =>
      (.terminalBody, [.wordStart, .bit false, .bit false])
  | .guard .sourceAtom, .bit true =>
      (.sourceAtomRoute,
        [.wordStart, .bit true, .bit false, .bit false])
  | .guard kind, .bit false => (.discard kind, [])
  | .guard kind, .wordEnd => (.between kind.next, [])
  | .terminalBody, .bit bit => (.terminalBody, [.bit bit])
  | .terminalBody, .wordEnd =>
      (.between .sourceAtom, [.wordEnd])
  | .sourceAtomRoute, .bit false =>
      (.sourceAtomRoute, [.bit false])
  | .sourceAtomRoute, .bit true =>
      (.sourceAtomSkip, [.bit true])
  | .sourceAtomRoute, .wordEnd =>
      (.between .terminal, [.wordEnd])
  | .sourceAtomSkip, .bit _ => (.sourceAtomSkip, [])
  | .sourceAtomSkip, .wordEnd =>
      (.between .terminal, [.wordEnd])
  | .discard kind, .wordEnd => (.between kind.next, [])
  | .discard kind, _ => (.discard kind, [])
  | control, _ => (control, [])

def finish (_ : Control) : List DelimitedBinaryWords.Token := []

def tokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output (.between .terminal) transition finish source

end RoutedVariableCompactAtomWordCleanup
end LeanTrominoes.PeriodicOrthocrossing
