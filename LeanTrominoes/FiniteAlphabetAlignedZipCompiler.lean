/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinCompiler
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinSemantics
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Pairing independently compiled aligned finite columns -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetAlignedZip

open Computability Turing FiniteAlphabetDelimitedBlockJoin

variable {First Second : Type}

abbrev Input (First Second : Type) := Token (First ⊕ Second)

def firstBlock (first : First) : List (Input First Second) :=
  [.value (.inl first), .blockEnd]

def secondBlock (second : Second) : List (Input First Second) :=
  [.value (.inr second), .blockEnd]

def pairBlock (pair : First × Second) : List (Input First Second) :=
  [.value (.inl pair.1), .value (.inr pair.2), .blockEnd]

def transition (state : Option First) : Input First Second → Option First × List (First × Second)
  | .value (.inl first) => (some first, [])
  | .value (.inr second) => (none, state.toList.map (fun first => (first, second)))
  | .blockEnd => (none, [])

def finish (_ : Option First) : List (First × Second) := []

def decoded (tokens : List (Input First Second)) : List (First × Second) :=
  FiniteStateTransducer.output none transition finish tokens

private theorem scan_pairBlock (pair : First × Second) :
    FiniteStateTransducer.scan transition none (pairBlock pair) = (none, [pair]) := by
  cases pair
  simp [pairBlock, FiniteStateTransducer.scan, transition]

private theorem decoded_pairBlock_append (pair : First × Second)
    (remaining : List (Input First Second)) :
    decoded (pairBlock pair ++ remaining) = pair :: decoded remaining := by
  unfold decoded FiniteStateTransducer.output
  rw [FiniteStateTransducer.scan_append, scan_pairBlock]
  simp [finish]

private theorem decoded_pairBlocks (pairs : List (First × Second)) :
    decoded (pairs.flatMap pairBlock) = pairs := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      rw [List.flatMap_cons, decoded_pairBlock_append, induction]

variable [Fintype First] [Fintype Second]

private theorem joined_pairBlocks (firsts : List First) (seconds : List Second)
    (aligned : firsts.length = seconds.length) :
    joined (firsts.flatMap firstBlock) (seconds.flatMap secondBlock) =
      (firsts.zip seconds).flatMap pairBlock := by
  let pairs := firsts.zip seconds
  have firstProjection : pairs.map (fun pair => [(Sum.inl pair.1 : First ⊕ Second)]) =
      firsts.map (fun first => [(Sum.inl first : First ⊕ Second)]) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun xs : List First => xs.map (fun first => [(Sum.inl first : First ⊕ Second)]))
        (List.map_fst_zip (l₁ := firsts) (l₂ := seconds) (by omega))
  have secondProjection : pairs.map (fun pair => [(Sum.inr pair.2 : First ⊕ Second)]) =
      seconds.map (fun second => [(Sum.inr second : First ⊕ Second)]) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun xs : List Second => xs.map (fun second => [(Sum.inr second : First ⊕ Second)]))
        (List.map_snd_zip (l₁ := firsts) (l₂ := seconds) (by omega))
  have exact := joined_pairedBlocks
    (pairs.map (fun pair => ([(Sum.inl pair.1 : First ⊕ Second)], [(Sum.inr pair.2 : First ⊕ Second)])))
  simp only [List.map_map, Function.comp_def] at exact
  rw [firstProjection, secondProjection] at exact
  unfold firstBlock secondBlock pairBlock
  simpa only [blocks, block, List.flatMap_map, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, pairs] using exact

def output (firsts : List First) (seconds : List Second) : List (First × Second) :=
  decoded (joined (firsts.flatMap firstBlock) (seconds.flatMap secondBlock))

theorem output_eq_zip (firsts : List First) (seconds : List Second)
    (aligned : firsts.length = seconds.length) :
    output firsts seconds = firsts.zip seconds := by
  unfold output
  rw [joined_pairBlocks firsts seconds aligned, decoded_pairBlocks]

variable [Inhabited First] [Inhabited Second]

/-- Any two polynomial-time finite columns of equal length can be zipped
under their native list encoding. -/
noncomputable def computableInPolyTimeOf
    {Source InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (firsts : Source → List First) (seconds : Source → List Second)
    (aligned : ∀ source, (firsts source).length = (seconds source).length)
    (firstCompiler : TM2ComputableInPolyTime encodeSource id firsts)
    (secondCompiler : TM2ComputableInPolyTime encodeSource id seconds) :
    TM2ComputableInPolyTime encodeSource id (fun source => (firsts source).zip (seconds source)) := by
  let firstTokens := TM2CompositionMachine.computableInPolyTime firstCompiler
    (FiniteBlockTransducer.computableInPolyTime (firstBlock (Second := Second)))
  let secondTokens := TM2CompositionMachine.computableInPolyTime secondCompiler
    (FiniteBlockTransducer.computableInPolyTime (secondBlock (First := First)))
  let joinedCompiler := joinedComputableInPolyTimeOf encodeSource
    (fun source => (firsts source).flatMap firstBlock)
    (fun source => (seconds source).flatMap secondBlock) firstTokens secondTokens
  let decoder := FiniteStateTransducer.computableInPolyTime
    (none : Option First) (transition (Second := Second)) finish
  let compiler := TM2CompositionMachine.computableInPolyTime joinedCompiler decoder
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler
    (fun source => output_eq_zip (firsts source) (seconds source) (aligned source))

end LeanTrominoes.FiniteAlphabetAlignedZip

end
