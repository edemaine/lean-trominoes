/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineIndexedEmitterData
import LeanTrominoes.RetainedInputAppendPipeline

/-! # Semantic pipelines of indexed affine-record phases -/

namespace LeanTrominoes
namespace GadgetSparseAffineIndexedEmitter

abbrev PhaseWorkspace (Data : Type) :=
  Data ⊕ GadgetSparseAffineVertexTokens.Token

/-- Lift a record family to a retained workspace.  Previously emitted tokens
are ignored and do not advance the selected-position counter. -/
def workspaceFamily {Data : Type} (family : RecordFamily Data) :
    RecordFamily (PhaseWorkspace Data)
  | .inl datum => family datum
  | .inr _ => none

theorem recordsEmittedAux_workspaceFamily
    {Data : Type} (family : RecordFamily Data)
    (position : Nat) (workspace : List (PhaseWorkspace Data)) :
    recordsEmittedAux (workspaceFamily family) position workspace =
      recordsEmittedAux family position
        (RetainedInputAppendPipeline.source workspace) := by
  induction workspace generalizing position with
  | nil => rfl
  | cons item workspace induction =>
      cases item with
      | inl datum =>
          cases familyEq : family datum with
          | none =>
              simp [recordsEmittedAux, workspaceFamily,
                RetainedInputAppendPipeline.source, familyEq, induction]
          | some templates =>
              simp [recordsEmittedAux, workspaceFamily,
                RetainedInputAppendPipeline.source, familyEq, induction]
      | inr token =>
          simp [recordsEmittedAux, workspaceFamily,
            RetainedInputAppendPipeline.source, induction]

@[simp] theorem recordsEmitted_workspaceFamily
    {Data : Type} (family : RecordFamily Data)
    (workspace : List (PhaseWorkspace Data)) :
    recordsEmitted (workspaceFamily family) workspace =
      recordsEmitted family
        (RetainedInputAppendPipeline.source workspace) := by
  exact recordsEmittedAux_workspaceFamily family 0 workspace

/-- Flatten the nested workspace produced by applying the one-phase indexed
emitter to an existing retained workspace. -/
def flattenItem {Data : Type} :
    (PhaseWorkspace Data ⊕ GadgetSparseAffineVertexTokens.Token) →
      List (PhaseWorkspace Data)
  | .inl item => [item]
  | .inr token => [.inr token]

def flattenWorkspace {Data : Type}
    (workspace : List
      (PhaseWorkspace Data ⊕ GadgetSparseAffineVertexTokens.Token)) :
    List (PhaseWorkspace Data) :=
  workspace.flatMap flattenItem

/-- One semantic phase retains its complete workspace and appends the record
word computed only from retained data. -/
def phaseRun {Data : Type} (family : RecordFamily Data)
    (workspace : List (PhaseWorkspace Data)) :
    List (PhaseWorkspace Data) :=
  RetainedInputAppendPipeline.appendFromWorkspace
    (recordsEmitted family) workspace

theorem flattenWorkspace_recordsAppended
    {Data : Type} (family : RecordFamily Data)
    (workspace : List (PhaseWorkspace Data)) :
    flattenWorkspace
        (workspace.map Sum.inl ++
          (recordsEmitted (workspaceFamily family) workspace).map Sum.inr) =
      phaseRun family workspace := by
  unfold flattenWorkspace phaseRun
    RetainedInputAppendPipeline.appendFromWorkspace
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map,
    recordsEmitted_workspaceFamily]
  simp [flattenItem]
  rw [← List.map_eq_flatMap]

/-- Execute indexed record phases from left to right on one shared retained
workspace. -/
def runPhases {Data : Type} :
    List (RecordFamily Data) → List (PhaseWorkspace Data) →
      List (PhaseWorkspace Data)
  | [], workspace => workspace
  | family :: families, workspace =>
      runPhases families (phaseRun family workspace)

def embedData {Data : Type} (data : List Data) :
    List (PhaseWorkspace Data) :=
  RetainedInputAppendPipeline.embed data

def extractRecords {Data : Type}
    (workspace : List (PhaseWorkspace Data)) :
    List GadgetSparseAffineVertexTokens.Token :=
  RetainedInputAppendPipeline.extract workspace

/-- Concatenated record word specified independently by every phase. -/
def phaseOutputs {Data : Type}
    (families : List (RecordFamily Data)) (data : List Data) :
    List GadgetSparseAffineVertexTokens.Token :=
  families.flatMap fun family => recordsEmitted family data

theorem runPhases_appended {Data : Type}
    (families : List (RecordFamily Data))
    (output : List Data → List GadgetSparseAffineVertexTokens.Token)
    (data : List Data) :
    runPhases families
        (RetainedInputAppendPipeline.appended output data) =
      RetainedInputAppendPipeline.appended
        (fun source => output source ++ phaseOutputs families source)
        data := by
  induction families generalizing output with
  | nil =>
      simp [runPhases, phaseOutputs,
        RetainedInputAppendPipeline.appended]
  | cons family families induction =>
      rw [runPhases, show phaseRun family
          (RetainedInputAppendPipeline.appended output data) =
        RetainedInputAppendPipeline.appended
          (fun source => output source ++ recordsEmitted family source)
          data by
        exact RetainedInputAppendPipeline.appendFromWorkspace_appended
          output (recordsEmitted family) data]
      rw [induction]
      simp only [phaseOutputs, List.flatMap_cons, List.append_assoc]

/-- Final record word emitted by a fixed sequence of indexed phases. -/
def emittedPhases {Data : Type}
    (families : List (RecordFamily Data)) (data : List Data) :
    List GadgetSparseAffineVertexTokens.Token :=
  extractRecords (runPhases families (embedData data))

@[simp] theorem emittedPhases_eq_phaseOutputs {Data : Type}
    (families : List (RecordFamily Data)) (data : List Data) :
    emittedPhases families data = phaseOutputs families data := by
  unfold emittedPhases embedData extractRecords
  have run := runPhases_appended families
    (fun _ : List Data => []) data
  simpa [RetainedInputAppendPipeline.appended] using congrArg
    RetainedInputAppendPipeline.extract run

end GadgetSparseAffineIndexedEmitter
end LeanTrominoes
