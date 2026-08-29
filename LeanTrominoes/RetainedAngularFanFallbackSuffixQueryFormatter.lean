/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteRoleSlotUnaryDecoderSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionBatchCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Formatting unary fallback-suffix queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixQueryFormatter

open Computability Turing FiniteStateTransducer
open FallbackSuffixDirectionCompiler
open FallbackSuffixDirectionCompiler.Batch

abbrev Symbol := UnaryFieldEncoderMachine.Symbol
abbrev HeaderRole :=
  RetainedFallbackFanKind × RetainedTerminalDirection

/-- The finite role and bounded slot occupy one unary field. -/
def headerCode (query : Query) : Nat :=
  8 * (Fintype.equivFin HeaderRole
      (query.kind, query.direction)).val +
    query.slot.val

/-- Each query is represented by its header code and raw radial length. -/
def queryCodes (queries : List Query) : List Nat :=
  queries.flatMap fun query => [headerCode query, query.rawLength]

structure Control where
  readingRadial : Bool
  header : FiniteRoleSlotUnaryDecoder.Control HeaderRole
  deriving DecidableEq, Fintype

def initial : Control :=
  ⟨false, FiniteRoleSlotUnaryDecoder.zero⟩

instance : Inhabited Control := ⟨initial⟩

def headerTokens
    (decoded : FiniteRoleSlotUnaryDecoder.Pair HeaderRole) :
    List FallbackSuffixDirectionCompiler.Token :=
  [.kind decoded.1.1, .terminalDirection decoded.1.2,
    .slot decoded.2]

def transition (control : Control) :
    Symbol → Control × List FallbackSuffixDirectionCompiler.Token
  | .unit =>
      if control.readingRadial then
        (control, [.radialUnit])
      else
        (⟨false,
            FiniteRoleSlotUnaryDecoder.increment control.header⟩, [])
  | .delimiter =>
      if control.readingRadial then
        (initial, [.queryEnd])
      else
        (⟨true, FiniteRoleSlotUnaryDecoder.zero⟩,
          headerTokens
            (FiniteRoleSlotUnaryDecoder.decode control.header))

def finish (_ : Control) :
    List FallbackSuffixDirectionCompiler.Token := []

def output (symbols : List Symbol) :
    List FallbackSuffixDirectionCompiler.Token :=
  FiniteStateTransducer.output initial transition finish symbols

private theorem scan_headerField
    (control : FiniteRoleSlotUnaryDecoder.Control HeaderRole)
    (code : Nat) :
    scan transition ⟨false, control⟩
        (UnaryFieldEncoderMachine.unaryField code) =
      (⟨true, FiniteRoleSlotUnaryDecoder.zero⟩,
        headerTokens
          (FiniteRoleSlotUnaryDecoder.decode
            (FiniteRoleSlotUnaryDecoder.advance control code))) := by
  induction code generalizing control with
  | zero => rfl
  | succ code induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [scan, transition, Bool.false_eq_true, if_false]
      rw [← UnaryFieldEncoderMachine.unaryField]
      simpa only [FiniteRoleSlotUnaryDecoder.advance_succ,
        List.nil_append] using
        induction (FiniteRoleSlotUnaryDecoder.increment control)

private theorem scan_radialField (length : Nat) :
    scan transition
        ⟨true, FiniteRoleSlotUnaryDecoder.zero⟩
        (UnaryFieldEncoderMachine.unaryField length) =
      (initial,
        List.replicate length
            FallbackSuffixDirectionCompiler.Token.radialUnit ++
          [.queryEnd]) := by
  induction length with
  | zero => rfl
  | succ length induction =>
      rw [UnaryFieldEncoderMachine.unaryField,
        List.replicate_succ, List.cons_append]
      simp only [scan, transition, if_true]
      rw [← UnaryFieldEncoderMachine.unaryField, induction]
      simp [List.replicate_succ]

private theorem decode_headerCode (query : Query) :
    FiniteRoleSlotUnaryDecoder.decode
        (FiniteRoleSlotUnaryDecoder.boundedCode
          (Role := HeaderRole) (headerCode query)) =
      ((query.kind, query.direction), query.slot) := by
  exact FiniteRoleSlotUnaryDecoder.decode_role_slot_index
    (query.kind, query.direction) query.slot

private theorem scan_query (query : Query) :
    scan transition initial
        (UnaryFieldEncoderMachine.unaryFields
          [headerCode query, query.rawLength]) =
      (initial,
        queryTokens query.kind query.direction query.rawLength query.slot) := by
  rw [UnaryFieldEncoderMachine.unaryFields_cons,
    UnaryFieldEncoderMachine.unaryFields_cons,
    UnaryFieldEncoderMachine.unaryFields_nil, List.append_nil]
  unfold initial
  rw [scan_append, scan_headerField]
  dsimp only
  have advanceZero :
      FiniteRoleSlotUnaryDecoder.advance
          (FiniteRoleSlotUnaryDecoder.zero (Role := HeaderRole))
          (headerCode query) =
        FiniteRoleSlotUnaryDecoder.boundedCode (headerCode query) := by
    simpa [FiniteRoleSlotUnaryDecoder.zero] using
      (FiniteRoleSlotUnaryDecoder.advance_boundedCode
        (Role := HeaderRole) 0 (headerCode query))
  rw [advanceZero, decode_headerCode, scan_radialField]
  simp [initial, headerTokens, queryTokens]

theorem scan_queryCodes (queries : List Query) :
    scan transition initial
        (UnaryFieldEncoderMachine.unaryFields (queryCodes queries)) =
      (initial, Batch.encode queries) := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      rw [show queryCodes (query :: queries) =
          [headerCode query, query.rawLength] ++ queryCodes queries by
        rfl]
      rw [UnaryFieldEncoderMachine.unaryFields_append,
        scan_append, scan_query]
      dsimp only
      rw [induction]
      rfl

@[simp] theorem output_queryCodes (queries : List Query) :
    output (UnaryFieldEncoderMachine.unaryFields (queryCodes queries)) =
      Batch.encode queries := by
  unfold output FiniteStateTransducer.output
  rw [scan_queryCodes]
  simp [finish]

private noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime id id output :=
  FiniteStateTransducer.computableInPolyTime initial transition finish

/-- Alternating unary header/radial fields format as exact compact suffix
queries in polynomial time. -/
noncomputable def encodeComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun queries =>
        UnaryFieldEncoderMachine.unaryFields (queryCodes queries))
      id Batch.encode :=
  TM2PolyTimeInputEncodingTransport.of_prepare
    (fun queries =>
      UnaryFieldEncoderMachine.unaryFields (queryCodes queries))
    outputComputableInPolyTime
    (fun _ => rfl) output_queryCodes

end FallbackSuffixQueryFormatter
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
