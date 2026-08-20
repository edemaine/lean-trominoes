/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAffineIndexedEmitterData
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time indexed compact affine vertex emitter -/

noncomputable section

namespace LeanTrominoes
namespace GadgetSparseAffineIndexedEmitter

open Computability Turing
open PeriodicCNF

abbrev Workspace (Data : Type) :=
  Data ⊕ GadgetSparseAffineVertexTokens.Token

instance workspaceInhabited {Data : Type} [Inhabited Data] :
    Inhabited (Workspace Data) :=
  ⟨.inl default⟩

/-- Translate one retained datum or one emitted unary-template token into the
compact affine vertex workspace. -/
def translateItem {Data : Type} :
    (Data ⊕ UnaryProgramTokens.Token) → List (Workspace Data)
  | .inl data => [.inl data]
  | .inr token => (tokenBlock token).map Sum.inr

@[simp] theorem translateItem_inl {Data : Type} (data : Data) :
    translateItem (.inl data) =
      [(.inl data : Workspace Data)] :=
  rfl

@[simp] theorem translateItem_inr {Data : Type}
    (token : UnaryProgramTokens.Token) :
    translateItem (Data := Data) (.inr token) =
      (tokenBlock token).map Sum.inr :=
  rfl

def translateWorkspace {Data : Type}
    (workspace : List (Data ⊕ UnaryProgramTokens.Token)) :
    List (Workspace Data) :=
  workspace.flatMap translateItem

/-- Semantic output of the translated indexed emitter. -/
def appendedOutput {Data : Type}
    (family : IndexedTemplateEmitter.Family Data)
    (data : List Data) : List (Workspace Data) :=
  data.map Sum.inl ++
    (translateTokens (IndexedTemplateEmitter.emitted family data)).map
      Sum.inr

@[simp] theorem translateWorkspace_indexed_appendedOutput
    {Data : Type} (family : IndexedTemplateEmitter.Family Data)
    (data : List Data) :
    translateWorkspace
        (IndexedTemplateEmitterMachine.appendedOutput family data) =
      appendedOutput family data := by
  unfold translateWorkspace appendedOutput
    IndexedTemplateEmitterMachine.appendedOutput
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map]
  simp [translateItem, translateTokens,
    List.map_flatMap]
  rw [← List.map_eq_flatMap]

/-- The fixed token translator is polynomial time. -/
noncomputable def translateComputableInPolyTime
    {Data : Type} [Fintype Data] [Inhabited Data] :
    @TM2ComputableInPolyTime
      (List (Data ⊕ UnaryProgramTokens.Token))
      (List (Workspace Data))
      (Data ⊕ UnaryProgramTokens.Token) (Workspace Data) id id
      (translateWorkspace (Data := Data)) :=
  FiniteBlockTransducer.computableInPolyTime translateItem

/-- Every fixed finite data-indexed affine-record family has a polynomial-time
retained-input compact vertex emitter. -/
noncomputable def computableInPolyTime
    {Data : Type} [Fintype Data] [Inhabited Data]
    (family : IndexedTemplateEmitter.Family Data) :
    @TM2ComputableInPolyTime
      (List Data) (List (Workspace Data))
      Data (Workspace Data) id id (appendedOutput family) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (IndexedTemplateEmitterMachine.computableInPolyTime family)
    (translateComputableInPolyTime (Data := Data))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (translateWorkspace_indexed_appendedOutput family)

/-- Semantic output specialized to the compact records described directly by
an affine record family. -/
def recordsAppendedOutput {Data : Type}
    (family : RecordFamily Data) (data : List Data) :
    List (Workspace Data) :=
  data.map Sum.inl ++ (recordsEmitted family data).map Sum.inr

@[simp] theorem appendedOutput_recipeFamily_eq_records
    {Data : Type} (family : RecordFamily Data) (data : List Data) :
    appendedOutput (recipeFamily family) data =
      recordsAppendedOutput family data := by
  simp [appendedOutput, recordsAppendedOutput]

/-- Every fixed finite family of affine compact records has a polynomial-time
retained-input emitter with its result stated directly as compact records. -/
noncomputable def recordsComputableInPolyTime
    {Data : Type} [Fintype Data] [Inhabited Data]
    (family : RecordFamily Data) :
    @TM2ComputableInPolyTime
      (List Data) (List (Workspace Data))
      Data (Workspace Data) id id (recordsAppendedOutput family) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (computableInPolyTime (recipeFamily family))
    (appendedOutput_recipeFamily_eq_records family)

end GadgetSparseAffineIndexedEmitter
end LeanTrominoes
