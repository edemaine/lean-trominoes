/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordData

/-! # Boundary-role crossover compact atom-word decoration -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossoverCompactAtomWords

open Computability Turing

inductive BoundaryPhase
  | between
  | guard
  | route
  | segment
  | retain
  | discard
  deriving DecidableEq, Fintype, Inhabited

inductive BoundaryAmount
  | zero
  | one
  | two
  | three
  deriving DecidableEq, Fintype, Inhabited

def BoundaryAmount.value : BoundaryAmount → Nat
  | .zero => 0
  | .one => 1
  | .two => 2
  | .three => 3

def BoundaryAmount.tokens : BoundaryAmount →
    List DelimitedBinaryWords.Token
  | .zero => []
  | .one => [.bit false]
  | .two => [.bit false, .bit false]
  | .three => [.bit false, .bit false, .bit false]

@[simp] theorem BoundaryAmount.tokens_eq_replicate
    (amount : BoundaryAmount) :
    amount.tokens =
      List.replicate amount.value (DelimitedBinaryWords.Token.bit false) := by
  cases amount <;> rfl

abbrev BoundaryControl := BoundaryAmount × BoundaryPhase

def sideAmount : CrossingSide → BoundaryAmount
  | .left => .zero
  | .right => .one
  | .top => .two
  | .bottom => .three

@[simp] theorem sideAmount_value (side : CrossingSide) :
    (sideAmount side).value = sourceSideIncrement side := by
  cases side <;> rfl

/-- One closed finite transition table for all four boundary roles. -/
def boundaryTransition :
    BoundaryControl → DelimitedBinaryWords.Token →
    BoundaryControl × List DelimitedBinaryWords.Token
  | (amount, .between), .wordStart => ((amount, .guard), [])
  | (amount, .guard), .bit true =>
      ((amount, .route), [.wordStart, .bit false, .bit true])
  | (amount, .guard), .bit false => ((amount, .discard), [])
  | (amount, .guard), .wordEnd => ((amount, .between), [])
  | (amount, .route), .bit false => ((amount, .route), [.bit false])
  | (amount, .route), .bit true => ((amount, .segment), [.bit true])
  | (amount, .route), .wordEnd => ((amount, .between), [.wordEnd])
  | (amount, .segment), .bit false =>
      ((amount, .segment), [.bit false])
  | (amount, .segment), .bit true =>
      ((amount, .retain), amount.tokens ++ [.bit true])
  | (amount, .segment), .wordEnd =>
      ((amount, .between), [.wordEnd])
  | (amount, .retain), .wordEnd =>
      ((amount, .between), [.wordEnd])
  | (amount, .retain), token => ((amount, .retain), [token])
  | (amount, .discard), .wordEnd => ((amount, .between), [])
  | (amount, .discard), _ => ((amount, .discard), [])
  | control, _ => (control, [])

def boundaryFinish (_ : BoundaryControl) :
    List DelimitedBinaryWords.Token := []

def boundaryTokens (side : CrossingSide)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output (sideAmount side, .between)
    boundaryTransition boundaryFinish source

opaque boundaryTokensComputableInPolyTime (side : CrossingSide) :
    TM2ComputableInPolyTime id id (boundaryTokens side) := by
  unfold boundaryTokens
  exact FiniteStateTransducer.computableInPolyTime
    (sideAmount side, BoundaryPhase.between)
    boundaryTransition boundaryFinish

private theorem scan_boundaryRetain
    (amount : BoundaryAmount) (bits : List Bool) :
    FiniteStateTransducer.scan boundaryTransition (amount, .retain)
        (bits.map .bit ++ [.wordEnd]) =
      ((amount, .between), bits.map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, boundaryTransition]
      rw [induction]
      rfl

private theorem scan_boundarySegment
    (amount : BoundaryAmount) (bits : List Bool) :
    FiniteStateTransducer.scan boundaryTransition (amount, .segment)
        (bits.map .bit ++ [.wordEnd]) =
      ((amount, .between),
        (retagFirstSegmentAfterRoute amount.value bits).map .bit ++
          [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit
      · simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, boundaryTransition,
          retagFirstSegmentAfterRoute]
        rw [induction]
        rfl
      · simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, boundaryTransition,
          retagFirstSegmentAfterRoute]
        rw [scan_boundaryRetain]
        simp [List.map_append]

private theorem scan_boundaryRoute
    (amount : BoundaryAmount) (bits : List Bool) :
    FiniteStateTransducer.scan boundaryTransition (amount, .route)
        (bits.map .bit ++ [.wordEnd]) =
      ((amount, .between),
        (retagFirstSegment amount.value bits).map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      cases bit
      · simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, boundaryTransition,
          retagFirstSegment]
        rw [induction]
        rfl
      · simp only [List.map_cons, List.cons_append,
          FiniteStateTransducer.scan, boundaryTransition,
          retagFirstSegment]
        rw [scan_boundarySegment]
        rfl

private theorem scan_boundaryDiscard
    (amount : BoundaryAmount) (bits : List Bool) :
    FiniteStateTransducer.scan boundaryTransition (amount, .discard)
        (bits.map .bit ++ [.wordEnd]) = ((amount, .between), []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, boundaryTransition]
      exact induction

def boundaryWord (amount : Nat) : List Bool → List (List Bool)
  | true :: sourcePair =>
      [[false, true] ++ retagFirstSegment amount sourcePair]
  | _ => []

@[simp] theorem boundaryTokens_wordTokens
    (side : CrossingSide) (guarded : List Bool) :
    boundaryTokens side (DelimitedBinaryWords.wordTokens guarded) =
      DelimitedBinaryWords.encode
        ⟨boundaryWord (sourceSideIncrement side) guarded⟩ := by
  unfold boundaryTokens FiniteStateTransducer.output
  cases guarded with
  | nil => rfl
  | cons active bits =>
      cases active
      · simp only [DelimitedBinaryWords.wordTokens, List.map_cons,
          List.cons_append, FiniteStateTransducer.scan,
          boundaryTransition, boundaryWord]
        rw [scan_boundaryDiscard]
        rfl
      · simp only [DelimitedBinaryWords.wordTokens, List.map_cons,
          List.cons_append, FiniteStateTransducer.scan,
          boundaryTransition, boundaryWord, DelimitedBinaryWords.encode,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [scan_boundaryRoute]
        simp [boundaryFinish]

end CrossoverCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing

end
