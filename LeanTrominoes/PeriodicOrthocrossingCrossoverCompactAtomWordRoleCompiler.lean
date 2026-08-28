/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordData
import LeanTrominoes.TM2CompositionMachine

/-! # One-role crossover compact atom-word decoration -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossoverCompactAtomWords

open Computability Turing
open PeriodicCNFStripReduction.DirectSourceFinalAtomWords
open PlanarThreeSAT

inductive CleanupControl
  | between
  | guard
  | retain
  | discard
  deriving DecidableEq, Fintype, Inhabited

/-- Fixed cleanup for a boundary-role source-key pair. -/
def boundaryTransition : CleanupControl → DelimitedBinaryWords.Token →
    CleanupControl × List DelimitedBinaryWords.Token
  | .between, .wordStart => (.guard, [])
  | .guard, .bit true =>
      (.retain, [.wordStart, .bit false, .bit true])
  | .guard, .bit false => (.discard, [])
  | .guard, .wordEnd => (.between, [])
  | .retain, .wordEnd => (.between, [.wordEnd])
  | .retain, token => (.retain, [token])
  | .discard, .wordEnd => (.between, [])
  | .discard, _ => (.discard, [])
  | control, _ => (control, [])

/-- Fixed cleanup for an internal-role source-key pair. -/
def internalTransition : CleanupControl → DelimitedBinaryWords.Token →
    CleanupControl × List DelimitedBinaryWords.Token
  | .between, .wordStart => (.guard, [])
  | .guard, .bit true =>
      (.retain, [.wordStart, .bit true, .bit true])
  | .guard, .bit false => (.discard, [])
  | .guard, .wordEnd => (.between, [])
  | .retain, .wordEnd => (.between, [.wordEnd])
  | .retain, token => (.retain, [token])
  | .discard, .wordEnd => (.between, [])
  | .discard, _ => (.discard, [])
  | control, _ => (control, [])

def cleanupFinish (_ : CleanupControl) :
    List DelimitedBinaryWords.Token := []

def boundaryTokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output .between
    boundaryTransition cleanupFinish source

def internalTokens (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  FiniteStateTransducer.output .between
    internalTransition cleanupFinish source

noncomputable def boundaryTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id boundaryTokens := by
  unfold boundaryTokens
  exact FiniteStateTransducer.computableInPolyTime
    CleanupControl.between boundaryTransition cleanupFinish

noncomputable def internalTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id internalTokens := by
  unfold internalTokens
  exact FiniteStateTransducer.computableInPolyTime
    CleanupControl.between internalTransition cleanupFinish

private theorem scan_boundaryRetain (bits : List Bool) :
    FiniteStateTransducer.scan boundaryTransition .retain
        (bits.map .bit ++ [.wordEnd]) =
      (.between, bits.map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, boundaryTransition]
      rw [induction]
      rfl

private theorem scan_internalRetain (bits : List Bool) :
    FiniteStateTransducer.scan internalTransition .retain
        (bits.map .bit ++ [.wordEnd]) =
      (.between, bits.map .bit ++ [.wordEnd]) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, internalTransition]
      rw [induction]
      rfl

private theorem scan_boundaryDiscard (bits : List Bool) :
    FiniteStateTransducer.scan boundaryTransition .discard
        (bits.map .bit ++ [.wordEnd]) = (.between, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, boundaryTransition]
      exact induction

private theorem scan_internalDiscard (bits : List Bool) :
    FiniteStateTransducer.scan internalTransition .discard
        (bits.map .bit ++ [.wordEnd]) = (.between, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, internalTransition]
      exact induction

def boundaryWord : List Bool → List (List Bool)
  | true :: sourcePair => [[false, true] ++ sourcePair]
  | _ => []

def internalBaseWord : List Bool → List (List Bool)
  | true :: sourcePair => [[true, true] ++ sourcePair]
  | _ => []

@[simp] theorem boundaryTokens_wordTokens (guarded : List Bool) :
    boundaryTokens (DelimitedBinaryWords.wordTokens guarded) =
      DelimitedBinaryWords.encode ⟨boundaryWord guarded⟩ := by
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
        rw [scan_boundaryRetain]
        simp [cleanupFinish, DelimitedBinaryWords.wordTokens]

@[simp] theorem internalTokens_wordTokens (guarded : List Bool) :
    internalTokens (DelimitedBinaryWords.wordTokens guarded) =
      DelimitedBinaryWords.encode ⟨internalBaseWord guarded⟩ := by
  unfold internalTokens FiniteStateTransducer.output
  cases guarded with
  | nil => rfl
  | cons active bits =>
      cases active
      · simp only [DelimitedBinaryWords.wordTokens, List.map_cons,
          List.cons_append, FiniteStateTransducer.scan,
          internalTransition, internalBaseWord]
        rw [scan_internalDiscard]
        rfl
      · simp only [DelimitedBinaryWords.wordTokens, List.map_cons,
          List.cons_append, FiniteStateTransducer.scan,
          internalTransition, internalBaseWord, DelimitedBinaryWords.encode,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [scan_internalRetain]
        simp [cleanupFinish, DelimitedBinaryWords.wordTokens]

/-- Insert a fixed internal-role suffix immediately before every word end. -/
def suffixSubstitution (roleSuffix : List Bool) :
    DelimitedBinaryWords.Token → List DelimitedBinaryWords.Token
  | .wordEnd => roleSuffix.map .bit ++ [.wordEnd]
  | token => [token]

def appendSuffixTokens (roleSuffix : List Bool)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  source.flatMap (suffixSubstitution roleSuffix)

noncomputable def appendSuffixTokensComputableInPolyTime
    (roleSuffix : List Bool) :
    TM2ComputableInPolyTime id id (appendSuffixTokens roleSuffix) := by
  exact FiniteBlockTransducer.computableInPolyTime
    (suffixSubstitution roleSuffix)

@[simp] theorem appendSuffixTokens_wordTokens
    (roleSuffix bits : List Bool) :
    appendSuffixTokens roleSuffix
        (DelimitedBinaryWords.wordTokens bits) =
      DelimitedBinaryWords.wordTokens (bits ++ roleSuffix) := by
  have body :
      (bits.map DelimitedBinaryWords.Token.bit).flatMap
          (suffixSubstitution roleSuffix) =
        bits.map DelimitedBinaryWords.Token.bit := by
    induction bits with
    | nil => rfl
    | cons bit bits induction =>
        simp [suffixSubstitution, induction]
  simp [appendSuffixTokens, suffixSubstitution,
    DelimitedBinaryWords.wordTokens, body, List.map_append]

def roleTokens (role : CrossoverVariable)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  match internal? role with
  | none => boundaryTokens source
  | some internal =>
      appendSuffixTokens (crossoverInternalWord internal)
        (internalTokens source)

noncomputable def roleTokensComputableInPolyTime
    (role : CrossoverVariable) :
    TM2ComputableInPolyTime id id (roleTokens role) := by
  cases role <;>
    simp only [roleTokens, internal?]
  all_goals first
    | exact boundaryTokensComputableInPolyTime
    | exact TM2CompositionMachine.computableInPolyTime
        internalTokensComputableInPolyTime
        (appendSuffixTokensComputableInPolyTime _)

private theorem map_suffix_wordTokens
    (roleSuffix : List Bool) (words : List (List Bool)) :
    appendSuffixTokens roleSuffix (DelimitedBinaryWords.encode ⟨words⟩) =
      DelimitedBinaryWords.encode
        ⟨words.map fun bits => bits ++ roleSuffix⟩ := by
  induction words with
  | nil => rfl
  | cons bits words induction =>
      unfold DelimitedBinaryWords.encode at induction ⊢
      rw [List.flatMap_cons]
      unfold appendSuffixTokens at induction ⊢
      rw [List.flatMap_append, appendSuffixTokens_wordTokens, induction]
      rfl

@[simp] theorem roleTokens_wordTokens
    (role : CrossoverVariable) (guarded : List Bool) :
    roleTokens role (DelimitedBinaryWords.wordTokens guarded) =
      DelimitedBinaryWords.encode ⟨word role guarded⟩ := by
  cases role <;>
    simp only [roleTokens, internal?, word, constructorPrefix, suffix]
  all_goals first
    | exact boundaryTokens_wordTokens guarded
    | rw [internalTokens_wordTokens, map_suffix_wordTokens]
      cases guarded <;> rfl
      next active bits => cases active <;> rfl

end CrossoverCompactAtomWords
end LeanTrominoes.PeriodicOrthocrossing

end
