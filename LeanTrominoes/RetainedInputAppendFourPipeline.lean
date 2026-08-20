/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Four-pass retained-input append pipelines -/

noncomputable section

namespace LeanTrominoes
namespace RetainedInputAppendPipeline

open Computability Turing

/-- Compose one initial retained-source appender and three subsequent passes,
while retaining the source in the resulting workspace. -/
def appendedComputableInPolyTimeOfFourAppenders
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Target] [Inhabited (Workspace Source Target)]
    (first second third fourth : List Source → List Target)
    (firstAppender : TM2ComputableInPolyTime id id (appended first))
    (secondAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace second))
    (thirdAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace third))
    (fourthAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace fourth)) :
    TM2ComputableInPolyTime id id
      (appended fun input =>
        ((first input ++ second input) ++ third input) ++ fourth input) := by
  let firstTwo := TM2CompositionMachine.computableInPolyTime
    firstAppender secondAppender
  let firstThree := TM2CompositionMachine.computableInPolyTime
    firstTwo thirdAppender
  let allFour := TM2CompositionMachine.computableInPolyTime
    firstThree fourthAppender
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq allFour
    (fun input => by
      simp only [appendFromWorkspace_appended])

/-- Transport a retained four-pass pipeline to a pointwise-equal appended
output. -/
def appendedComputableInPolyTimeOfFourAppendersEq
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Target] [Inhabited (Workspace Source Target)]
    (first second third fourth output : List Source → List Target)
    (correct : ∀ input,
      ((first input ++ second input) ++ third input) ++ fourth input =
        output input)
    (firstAppender : TM2ComputableInPolyTime id id (appended first))
    (secondAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace second))
    (thirdAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace third))
    (fourthAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace fourth)) :
    TM2ComputableInPolyTime id id (appended output) :=
  computableInPolyTimeOfEq
    (appended fun input =>
      ((first input ++ second input) ++ third input) ++ fourth input)
    (appended output)
    (fun input => by
      unfold appended
      dsimp only
      rw [correct input])
    (appendedComputableInPolyTimeOfFourAppenders
      first second third fourth
      firstAppender secondAppender thirdAppender fourthAppender)

/-- Compose one initial retained-source appender and three subsequent passes,
then remove the retained source. -/
def computableInPolyTimeOfFourAppenders
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Target] [Inhabited (Workspace Source Target)]
    (first second third fourth : List Source → List Target)
    (firstAppender : TM2ComputableInPolyTime id id (appended first))
    (secondAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace second))
    (thirdAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace third))
    (fourthAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace fourth)) :
    TM2ComputableInPolyTime id id
      (fun input =>
        ((first input ++ second input) ++ third input) ++ fourth input) := by
  let firstTwo := TM2CompositionMachine.computableInPolyTime
    firstAppender secondAppender
  let firstThree := TM2CompositionMachine.computableInPolyTime
    firstTwo thirdAppender
  let allFour := TM2CompositionMachine.computableInPolyTime
    firstThree fourthAppender
  let extracted := TM2CompositionMachine.computableInPolyTime allFour
    (extractComputableInPolyTime (Source := Source) (Target := Target))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq extracted
    (fun input => by
      simp only [appendFromWorkspace_appended, extract_appended])

/-- Transport a four-pass pipeline to a pointwise-equal native output. -/
def computableInPolyTimeOfFourAppendersEq
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Target] [Inhabited (Workspace Source Target)]
    (first second third fourth output : List Source → List Target)
    (correct : ∀ input,
      ((first input ++ second input) ++ third input) ++ fourth input =
        output input)
    (firstAppender : TM2ComputableInPolyTime id id (appended first))
    (secondAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace second))
    (thirdAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace third))
    (fourthAppender : TM2ComputableInPolyTime id id
      (appendFromWorkspace fourth)) :
    TM2ComputableInPolyTime id id output :=
  computableInPolyTimeOfEq
    (fun input =>
      ((first input ++ second input) ++ third input) ++ fourth input)
    output correct
    (computableInPolyTimeOfFourAppenders first second third fourth
      firstAppender secondAppender thirdAppender fourthAppender)

end RetainedInputAppendPipeline
end LeanTrominoes
