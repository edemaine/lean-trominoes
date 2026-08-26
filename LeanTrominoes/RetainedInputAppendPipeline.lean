/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2NativeListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time pipelines that retain their original input -/

noncomputable section

namespace LeanTrominoes
namespace RetainedInputAppendPipeline

open Computability Turing

abbrev Workspace (Source Target : Type) := Source ⊕ Target

/-- Embed source symbols in the stable left side of a shared workspace. -/
def embed {Source Target : Type} (input : List Source) :
    List (Workspace Source Target) :=
  input.map Sum.inl

/-- Recover retained source symbols, ignoring appended target symbols. -/
def source {Source Target : Type}
    (workspace : List (Workspace Source Target)) : List Source :=
  workspace.flatMap fun
    | .inl symbol => [symbol]
    | .inr _ => []

/-- Extract appended target symbols, ignoring retained source symbols. -/
def extract {Source Target : Type}
    (workspace : List (Workspace Source Target)) : List Target :=
  workspace.flatMap fun
    | .inl _ => []
    | .inr token => [token]

/-- Retain one source word and append a derived target word. -/
def appended {Source Target : Type}
    (output : List Source → List Target) (input : List Source) :
    List (Workspace Source Target) :=
  embed input ++ (output input).map Sum.inr

/-- Append a second derived target word to a workspace, computing it only
from the retained source symbols. -/
def appendFromWorkspace {Source Target : Type}
    (output : List Source → List Target)
    (workspace : List (Workspace Source Target)) :
    List (Workspace Source Target) :=
  workspace ++ (output (source workspace)).map Sum.inr

@[simp] theorem source_embed {Source Target : Type}
    (input : List Source) :
    source (Target := Target) (embed input) = input := by
  unfold source embed
  rw [List.flatMap_map]
  simp

@[simp] theorem source_map_inr {Source Target : Type}
    (tokens : List Target) :
    source (Source := Source) (tokens.map Sum.inr) = [] := by
  unfold source
  rw [List.flatMap_map]
  simp

@[simp] theorem source_append {Source Target : Type}
    (first second : List (Workspace Source Target)) :
    source (first ++ second) = source first ++ source second := by
  simp [source]

@[simp] theorem source_appended {Source Target : Type}
    (output : List Source → List Target) (input : List Source) :
    source (appended output input) = input := by
  rw [appended, source_append, source_embed, source_map_inr,
    List.append_nil]

@[simp] theorem extract_embed {Source Target : Type}
    (input : List Source) :
    extract (Target := Target) (embed input) = [] := by
  unfold extract embed
  rw [List.flatMap_map]
  simp

@[simp] theorem extract_map_inr {Source Target : Type}
    (tokens : List Target) :
    extract (Source := Source) (tokens.map Sum.inr) = tokens := by
  unfold extract
  rw [List.flatMap_map]
  simp

@[simp] theorem extract_append {Source Target : Type}
    (first second : List (Workspace Source Target)) :
    extract (first ++ second) = extract first ++ extract second := by
  simp [extract]

@[simp] theorem extract_appended {Source Target : Type}
    (output : List Source → List Target) (input : List Source) :
    extract (appended output input) = output input := by
  rw [appended, extract_append, extract_embed, extract_map_inr,
    List.nil_append]

@[simp] theorem appendFromWorkspace_appended
    {Source Target : Type}
    (first second : List Source → List Target)
    (input : List Source) :
    appendFromWorkspace second (appended first input) =
      appended (fun source => first source ++ second source) input := by
  unfold appendFromWorkspace
  rw [source_appended]
  simp [appended, List.map_append, List.append_assoc]

/-- Fixed source embedding is polynomial time. -/
def embedComputableInPolyTime {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited (Workspace Source Target)] :
    TM2ComputableInPolyTime id id
      (embed : List Source → List (Workspace Source Target)) := by
  let machine := FiniteBlockTransducer.computableInPolyTime
    (fun symbol : Source => [(Sum.inl symbol : Workspace Source Target)])
  refine
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := ?_ }
  intro input
  have run := machine.outputsFun input
  have outputEq :
      input.flatMap
          (fun symbol : Source =>
            [(Sum.inl symbol : Workspace Source Target)]) =
        embed input := by
    rw [← List.map_eq_flatMap]
    rfl
  rw [outputEq] at run
  exact run

/-- Fixed target extraction is polynomial time. -/
def extractComputableInPolyTime {Source Target : Type}
    [Fintype Source] [Fintype Target] [Inhabited Target] :
    TM2ComputableInPolyTime id id
      (extract : List (Workspace Source Target) → List Target) :=
  FiniteBlockTransducer.computableInPolyTime fun
    | (Sum.inl _ : Workspace Source Target) => []
    | .inr token => [token]

/-- Retain the input beside the output of any native list compiler. -/
def appendedComputableInPolyTimeOfCompiler
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Target] [Inhabited (Workspace Source Target)]
    (output : List Source → List Target)
    (compiler : TM2ComputableInPolyTime id id output) :
    TM2ComputableInPolyTime id id (appended output) := by
  let lifted := TM2CompositionMachine.computableInPolyTime compiler
    (FiniteBlockTransducer.computableInPolyTime fun token : Target =>
      [(Sum.inr token : Workspace Source Target)])
  let complete := TM2ListAppend.nativeComputableInPolyTime
    (embedComputableInPolyTime (Source := Source) (Target := Target)) lifted
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    (fun input => by
      unfold appended
      rw [← List.map_eq_flatMap])

/-- Compose two retained-input appenders and remove the retained source. -/
def computableInPolyTimeOfAppenders
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Target] [Inhabited (Workspace Source Target)]
    (first second : List Source → List Target)
    (firstAppender : TM2ComputableInPolyTime id id (appended first))
    (secondAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace second)) :
    TM2ComputableInPolyTime id id
      (fun input => first input ++ second input) := by
  let appendedBoth := TM2CompositionMachine.computableInPolyTime
    firstAppender secondAppender
  let extracted := TM2CompositionMachine.computableInPolyTime appendedBoth
    (extractComputableInPolyTime (Source := Source) (Target := Target))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq extracted
    (fun input => by
      simp only [appendFromWorkspace_appended, extract_appended])

/-- Transport a retained-input two-pass pipeline to any pointwise-equal
combined output without exposing the composed machine record again. -/
def computableInPolyTimeOfAppendersEq
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Target] [Inhabited (Workspace Source Target)]
    (first second output : List Source → List Target)
    (correct : ∀ input, first input ++ second input = output input)
    (firstAppender : TM2ComputableInPolyTime id id (appended first))
    (secondAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace second)) :
    TM2ComputableInPolyTime id id output :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (computableInPolyTimeOfAppenders first second
      firstAppender secondAppender)
    correct

/-- Transport a native list transducer across a pointwise output equality. -/
def computableInPolyTimeOfEq
    {Source Target : Type}
    (first second : List Source → List Target)
    (correct : ∀ input, first input = second input)
    (compiler : TM2ComputableInPolyTime id id first) :
    TM2ComputableInPolyTime id id second :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiler correct

end RetainedInputAppendPipeline
end LeanTrominoes
