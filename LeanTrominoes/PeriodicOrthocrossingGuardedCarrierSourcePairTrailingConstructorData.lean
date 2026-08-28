/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeNormalizedSourceKeyData

/-! # Constructor classification of guarded carrier source pairs

The first source key stores the carrier-node constructor in the low three
bits of its segment field.  This finite-state pass copies the required atom
payload and delays the recovered constructor bit until the end of the word.
That delayed bit can subsequently be rotated to the front.
-/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairTrailingConstructor

inductive TagRemainder
  | zero | one | two | three | four | five | six | seven
  deriving DecidableEq, Fintype

def TagRemainder.next : TagRemainder → TagRemainder
  | .zero => .one
  | .one => .two
  | .two => .three
  | .three => .four
  | .four => .five
  | .five => .six
  | .six => .seven
  | .seven => .zero

def TagRemainder.advance (remainder : TagRemainder) : Nat → TagRemainder
  | 0 => remainder
  | number + 1 => advance remainder.next number

/-- Terminal tags are `0,1`; every other low-three-bit value is treated as a
boundary tag.  Canonical carrier source pairs use only tags `0,...,5`. -/
def TagRemainder.isBoundary : TagRemainder → Bool
  | .zero | .one => false
  | _ => true

inductive Control
  | between
  | guard
  | route
  | segment (remainder : TagRemainder)
  | horizontalSign (boundary : Bool)
  | horizontal (boundary : Bool)
  | verticalSign (boundary : Bool)
  | vertical (boundary : Bool)
  | separator (boundary : Bool)
  | second (boundary : Bool)
  deriving DecidableEq, Fintype, Inhabited

open DelimitedBinaryWords

/-- Remove the active guard, retain one key for a terminal or both keys for
a boundary, and append the recovered constructor bit just before `wordEnd`.
-/
def transition : Control → Token → Control × List Token
  | .between, .wordStart => (.guard, [.wordStart])
  | .between, _ => (.between, [])
  | .guard, .bit _ => (.route, [])
  | .guard, .wordEnd => (.between, [])
  | .guard, .wordStart => (.guard, [])
  | .route, .bit false => (.route, [.bit false])
  | .route, .bit true => (.segment .zero, [.bit true])
  | .route, .wordEnd => (.between, [.wordEnd])
  | .route, .wordStart => (.route, [])
  | .segment remainder, .bit false =>
      (.segment remainder.next, [.bit false])
  | .segment remainder, .bit true =>
      (.horizontalSign remainder.isBoundary, [.bit true])
  | .segment _, .wordEnd => (.between, [.wordEnd])
  | .segment remainder, .wordStart => (.segment remainder, [])
  | .horizontalSign boundary, .bit bit =>
      (.horizontal boundary, [.bit bit])
  | .horizontalSign _, .wordEnd => (.between, [.wordEnd])
  | .horizontalSign boundary, .wordStart =>
      (.horizontalSign boundary, [])
  | .horizontal boundary, .bit false =>
      (.horizontal boundary, [.bit false])
  | .horizontal boundary, .bit true =>
      (.verticalSign boundary, [.bit true])
  | .horizontal _, .wordEnd => (.between, [.wordEnd])
  | .horizontal boundary, .wordStart => (.horizontal boundary, [])
  | .verticalSign boundary, .bit bit =>
      (.vertical boundary, [.bit bit])
  | .verticalSign _, .wordEnd => (.between, [.wordEnd])
  | .verticalSign boundary, .wordStart =>
      (.verticalSign boundary, [])
  | .vertical boundary, .bit false =>
      (.vertical boundary, [.bit false])
  | .vertical boundary, .bit true =>
      (.separator boundary, [.bit true])
  | .vertical _, .wordEnd => (.between, [.wordEnd])
  | .vertical boundary, .wordStart => (.vertical boundary, [])
  | .separator boundary, .bit bit =>
      (.second boundary, if boundary then [.bit bit] else [])
  | .separator _, .wordEnd => (.between, [.wordEnd])
  | .separator boundary, .wordStart => (.separator boundary, [])
  | .second boundary, .bit bit =>
      (.second boundary, if boundary then [.bit bit] else [])
  | .second boundary, .wordEnd =>
      (.between, [.bit boundary, .wordEnd])
  | .second boundary, .wordStart => (.second boundary, [])

def finish (_ : Control) : List Token := []

def tokens (source : List Token) : List Token :=
  FiniteStateTransducer.output .between transition finish source

/-- The exact delayed-constructor payload associated with a normalized
carrier node. -/
def nodeWordAtPeriod (period : Nat) : CarrierNode → List Bool
  | .terminal terminal =>
      CarrierKeyWords.word
        (CarrierNodeNormalizedSourceKeys.pairAtPeriod
          period (.terminal terminal)).1 ++ [false]
  | .boundary boundary =>
      CarrierNodeSourceKeys.word
        (CarrierNodeNormalizedSourceKeys.pairAtPeriod
          period (.boundary boundary)) ++ [true]

def nodeWordsAtPeriod (period : Nat) (nodes : List CarrierNode) :
    DelimitedBinaryWords.Input :=
  ⟨nodes.map (nodeWordAtPeriod period)⟩

end GuardedCarrierSourcePairTrailingConstructor
end LeanTrominoes.PeriodicOrthocrossing
