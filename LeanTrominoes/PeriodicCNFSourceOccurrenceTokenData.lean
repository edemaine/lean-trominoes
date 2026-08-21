/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicCNFFlatEncoding

/-! # Finite occurrence tokens parsed from flat CNF fields -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTokens

open Turing

/-- Finite route-relevant presentation tokens.  Atom and horizontal-offset
values remain as binary bitstrings; clause and literal positions are bounded
by the width-three promise. -/
inductive Token
  | clause (arity : Fin 4)
  | literal (index : Fin 3)
  | atomBit (value : Bool)
  | atomEnd
  | offsetBit (value : Bool)
  | offsetEnd
  | literalEnd
  deriving DecidableEq, Fintype, Inhabited

inductive ArityState
  | start
  | lowZero
  | lowOne
  | valueZero
  | valueOne
  | valueTwo
  | valueThree
  | invalid
  deriving DecidableEq, Fintype

def ArityState.pushBit : ArityState → Bool → ArityState
  | .start, false => .lowZero
  | .start, true => .lowOne
  | .lowZero, false => .valueZero
  | .lowZero, true => .valueTwo
  | .lowOne, false => .valueOne
  | .lowOne, true => .valueThree
  | _, _ => .invalid

/-- Decode canonical binary arities zero through three; malformed bounded
fields fall back to zero. -/
def ArityState.value : ArityState → Fin 4
  | .start | .lowZero | .valueZero => 0
  | .lowOne | .valueOne => 1
  | .valueTwo => 2
  | .valueThree => 3
  | .invalid => 0

inductive LiteralField
  | atom
  | horizontalOffset
  | verticalOffset
  | polarity
  deriving DecidableEq, Fintype

/-- `remaining` is the number of literals after the current one. -/
inductive Control
  | clauseCount
  | arity (state : ArityState)
  | literal (remaining index : Fin 3) (field : LiteralField)
  deriving DecidableEq, Fintype

def initial : Control := .clauseCount

def clauseArity (arity : Nat) : Fin 4 :=
  Fin.ofNat 4 arity

def literalIndex (index : Nat) : Fin 3 :=
  Fin.ofNat 3 index

def beginClause (arity : Fin 4) : Control × List Token :=
  match arity.val with
  | 0 => (.arity .start, [.clause arity])
  | 1 => (.literal 0 0 .atom, [.clause arity, .literal 0])
  | 2 => (.literal 1 0 .atom, [.clause arity, .literal 0])
  | _ => (.literal 2 0 .atom, [.clause arity, .literal 0])

def nextLiteral (remaining index : Fin 3) : Control × List Token :=
  if remaining.val = 0 then
    (.arity .start, [.literalEnd])
  else
    let nextIndex := index + 1
    (.literal (remaining - 1) nextIndex .atom,
      [.literalEnd, .literal nextIndex])

def transition : Control → PeriodicCNFFlatEncoding.Symbol →
    Control × List Token
  | .clauseCount, .cons | .clauseCount, .consₗ =>
      (.arity .start, [])
  | .clauseCount, _ => (.clauseCount, [])
  | .arity state, .bit0 => (.arity (state.pushBit false), [])
  | .arity state, .bit1 => (.arity (state.pushBit true), [])
  | .arity state, .cons | .arity state, .consₗ =>
      beginClause state.value
  | .literal remaining index .atom, .bit0 =>
      (.literal remaining index .atom, [.atomBit false])
  | .literal remaining index .atom, .bit1 =>
      (.literal remaining index .atom, [.atomBit true])
  | .literal remaining index .atom, .cons |
      .literal remaining index .atom, .consₗ =>
      (.literal remaining index .horizontalOffset, [.atomEnd])
  | .literal remaining index .horizontalOffset, .bit0 =>
      (.literal remaining index .horizontalOffset, [.offsetBit false])
  | .literal remaining index .horizontalOffset, .bit1 =>
      (.literal remaining index .horizontalOffset, [.offsetBit true])
  | .literal remaining index .horizontalOffset, .cons |
      .literal remaining index .horizontalOffset, .consₗ =>
      (.literal remaining index .verticalOffset, [.offsetEnd])
  | .literal remaining index .verticalOffset, .cons |
      .literal remaining index .verticalOffset, .consₗ =>
      (.literal remaining index .polarity, [])
  | .literal remaining index .verticalOffset, _ =>
      (.literal remaining index .verticalOffset, [])
  | .literal remaining index .polarity, .cons |
      .literal remaining index .polarity, .consₗ =>
      nextLiteral remaining index
  | .literal remaining index .polarity, _ =>
      (.literal remaining index .polarity, [])

def finish (_ : Control) : List Token := []

/-- Physical finite-state parse of one flat formula word. -/
def parse (symbols : List PeriodicCNFFlatEncoding.Symbol) : List Token :=
  FiniteStateTransducer.output initial transition finish symbols

def nativeBit : PeriodicCNFFlatEncoding.Symbol → Bool
  | .bit1 => true
  | _ => false

def atomTokens (atom : Nat) : List Token :=
  (PartrecToTM2.trNat atom).map fun symbol => .atomBit (nativeBit symbol)

def offsetTokens (offset : Int) : List Token :=
  (PartrecToTM2.trNat (Encodable.encode offset)).map fun symbol =>
    .offsetBit (nativeBit symbol)

/-- Intended token block for one indexed semantic literal. -/
def literalTokens (index : Nat) (literal : PeriodicLiteral Nat) :
    List Token :=
  [.literal (literalIndex index)] ++
    atomTokens literal.atom ++ [.atomEnd] ++
    offsetTokens literal.offset.1 ++ [.offsetEnd, .literalEnd]

/-- Intended block for one width-three clause. -/
def clauseTokens (clause : PeriodicClause Nat) : List Token :=
  .clause (clauseArity clause.length) ::
    (clause.zipIdx.flatMap fun tagged =>
      literalTokens tagged.2 tagged.1)

/-- Exact intended occurrence stream of a semantic source formula. -/
def formulaTokens (formula : PeriodicCNF Nat) : List Token :=
  formula.clauses.flatMap clauseTokens

end SourceOccurrenceTokens
end PeriodicCNF
end LeanTrominoes
