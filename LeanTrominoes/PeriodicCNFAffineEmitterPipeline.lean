/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineTemplateEmitterTime
import LeanTrominoes.TM2CompositionMachine

/-!
# Polynomial-time pipelines of affine emitter phases

All concrete printer phases share one alphabet `Data ⊕ Token`: original
prepared symbols use the left injection and every emitted token uses the
right.  This file proves that earlier output never changes later selector
counts, composes any fixed phase list, and removes the retained prepared input
at the end.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace AffineEmitterPipeline

open AffineTemplateEmitterMachine
open UnaryProgramTokens

abbrev Workspace (Data : Type) := Data ⊕ Token

/-- One fixed pass of the affine-position emitter. -/
structure Phase (Data : Type) where
  selected : Data → Bool
  recipes : List Recipe
  ending : List Token

namespace Phase

def run {Data : Type} (phase : Phase Data) :
    List (Workspace Data) → List (Workspace Data) :=
  appendedOutput phase.selected phase.recipes phase.ending

/-- Token suffix contributed by a phase to one original data word. -/
def emitted {Data : Type} (phase : Phase Data) (data : List Data) :
    List Token :=
  positionRangeTokens phase.recipes 0
      (UnaryPolynomialPaddingMachine.selectedCount phase.selected data) ++
    phase.ending

noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (phase : Phase Data) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id phase.run :=
  AffineTemplateEmitterMachine.computableInPolyTime
    phase.selected phase.recipes phase.ending

end Phase

/-- Embed the prepared input into the stable shared alphabet. -/
def embedData {Data : Type} (data : List Data) : List (Workspace Data) :=
  data.map fun item => .inl item

/-- Delete retained prepared symbols and keep the emitted token stream. -/
def extractTokens {Data : Type} (workspace : List (Workspace Data)) :
    List Token :=
  workspace.flatMap fun
    | .inl _ => []
    | .inr token => [token]

theorem unarySelectedCount_append {Alphabet : Type}
    (selected : Alphabet → Bool) (first second : List Alphabet) :
    UnaryPolynomialPaddingMachine.selectedCount selected (first ++ second) =
      UnaryPolynomialPaddingMachine.selectedCount selected first +
        UnaryPolynomialPaddingMachine.selectedCount selected second := by
  induction first with
  | nil => simp [UnaryPolynomialPaddingMachine.selectedCount]
  | cons item first induction =>
      simp only [List.cons_append,
        UnaryPolynomialPaddingMachine.selectedCount_cons, induction]
      omega

theorem selectedCount_append {Data : Type} (selected : Data → Bool)
    (first second : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected (first ++ second) =
      AffineTemplateEmitterMachine.selectedCount selected first +
        AffineTemplateEmitterMachine.selectedCount selected second := by
  exact unarySelectedCount_append
    (AffineTemplateEmitterMachine.dataSelected selected) first second

@[simp]
theorem embedData_eq_map {Data : Type} (data : List Data) :
    embedData data =
      data.map fun item => (Sum.inl item : Workspace Data) :=
  rfl

theorem flatMap_singleton_eq_map {Source Target : Type}
    (function : Source → Target) (source : List Source) :
    source.flatMap (fun item => [function item]) = source.map function := by
  induction source with
  | nil => rfl
  | cons item source induction => simp [induction]

@[simp]
theorem selectedCount_embedData {Data : Type} (selected : Data → Bool)
    (data : List Data) :
    AffineTemplateEmitterMachine.selectedCount selected (embedData data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  unfold AffineTemplateEmitterMachine.selectedCount
  rw [embedData_eq_map]
  induction data with
  | nil => rfl
  | cons item data induction =>
      simp only [List.map_cons,
        UnaryPolynomialPaddingMachine.selectedCount_cons,
        AffineTemplateEmitterMachine.dataSelected, induction]
      rfl

@[simp]
theorem selectedCount_map_inr {Data : Type} (selected : Data → Bool)
    (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount selected
      (tokens.map fun token => (Sum.inr token : Workspace Data)) = 0 := by
  unfold AffineTemplateEmitterMachine.selectedCount
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp only [List.map_cons,
        UnaryPolynomialPaddingMachine.selectedCount_cons,
        AffineTemplateEmitterMachine.dataSelected, Bool.false_eq_true,
        if_false, Nat.zero_add, induction]

@[simp]
theorem selectedCount_embed_append_tokens {Data : Type}
    (selected : Data → Bool) (data : List Data) (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount selected
        (embedData data ++
          tokens.map fun token => (Sum.inr token : Workspace Data)) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  rw [selectedCount_append, selectedCount_embedData,
    selectedCount_map_inr, Nat.add_zero]

theorem Phase.run_embed_append_tokens {Data : Type} (phase : Phase Data)
    (data : List Data) (tokens : List Token) :
    phase.run
        (embedData data ++
          tokens.map fun token => (Sum.inr token : Workspace Data)) =
      embedData data ++
        (tokens ++ phase.emitted data).map fun token =>
          (Sum.inr token : Workspace Data) := by
  unfold Phase.run Phase.emitted
  rw [show appendedOutput phase.selected phase.recipes phase.ending
          (embedData data ++ tokens.map fun token =>
            (Sum.inr token : Workspace Data)) =
        (embedData data ++ tokens.map fun token =>
            (Sum.inr token : Workspace Data)) ++
          (positionRangeTokens phase.recipes 0
              (AffineTemplateEmitterMachine.selectedCount phase.selected
                (embedData data ++ tokens.map fun token =>
                  (Sum.inr token : Workspace Data))) ++
            phase.ending).map Sum.inr by rfl,
    selectedCount_embed_append_tokens]
  simp [List.map_append, List.append_assoc]

def runAll {Data : Type} :
    List (Phase Data) → List (Workspace Data) → List (Workspace Data)
  | [], workspace => workspace
  | phase :: phases, workspace => runAll phases (phase.run workspace)

def emittedAll {Data : Type} :
    List (Phase Data) → List Data → List Token
  | [], _ => []
  | phase :: phases, data => phase.emitted data ++ emittedAll phases data

theorem runAll_embed_append_tokens {Data : Type} (phases : List (Phase Data))
    (data : List Data) (tokens : List Token) :
    runAll phases
        (embedData data ++
          tokens.map fun token => (Sum.inr token : Workspace Data)) =
      embedData data ++
        (tokens ++ emittedAll phases data).map fun token =>
          (Sum.inr token : Workspace Data) := by
  induction phases generalizing tokens with
  | nil => simp [runAll, emittedAll]
  | cons phase phases induction =>
      rw [runAll, phase.run_embed_append_tokens, induction]
      simp [emittedAll, List.append_assoc]

@[simp]
theorem runAll_embedData {Data : Type} (phases : List (Phase Data))
    (data : List Data) :
    runAll phases (embedData data) =
      embedData data ++
        (emittedAll phases data).map fun token =>
          (Sum.inr token : Workspace Data) := by
  simpa using runAll_embed_append_tokens phases data []

@[simp]
theorem extractTokens_runAll_embedData {Data : Type}
    (phases : List (Phase Data)) (data : List Data) :
    extractTokens (runAll phases (embedData data)) =
      emittedAll phases data := by
  rw [runAll_embedData]
  rw [show extractTokens
          (embedData data ++
            (emittedAll phases data).map fun token =>
              (Sum.inr token : Workspace Data)) =
        extractTokens (embedData data) ++
          extractTokens ((emittedAll phases data).map fun token =>
            (Sum.inr token : Workspace Data)) by
      simp [extractTokens]]
  have left : extractTokens (embedData data) = [] := by
    rw [embedData_eq_map]
    induction data with
    | nil => rfl
    | cons item data induction =>
        change extractTokens
          (data.map fun item => (Sum.inl item : Workspace Data)) = []
        exact induction
  have right : extractTokens
      ((emittedAll phases data).map fun token =>
        (Sum.inr token : Workspace Data)) = emittedAll phases data := by
    induction emittedAll phases data with
    | nil => rfl
    | cons token tokens induction =>
        change token :: extractTokens
          (tokens.map fun token => (Sum.inr token : Workspace Data)) =
            token :: tokens
        rw [induction]
  rw [left, right, List.nil_append]

noncomputable def embedDataComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] :
    @TM2ComputableInPolyTime
      (List Data) (List (Workspace Data)) Data (Workspace Data)
      id id embedData := by
  let certificate := FiniteBlockTransducer.computableInPolyTime
    (fun item : Data => [(Sum.inl item : Workspace Data)])
  refine
    { tm := certificate.tm
      inputAlphabet := certificate.inputAlphabet
      outputAlphabet := certificate.outputAlphabet
      time := certificate.time
      outputsFun := ?_ }
  intro data
  have run := certificate.outputsFun data
  have outputEq :
      data.flatMap (fun item => [(Sum.inl item : Workspace Data)]) =
        embedData data := by
    rw [flatMap_singleton_eq_map]
    rfl
  rw [outputEq] at run
  exact run

noncomputable def extractTokensComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List Token) (Workspace Data) Token
      id id extractTokens :=
  FiniteBlockTransducer.computableInPolyTime
    (fun item : Workspace Data =>
      match item with
      | .inl _ => []
      | .inr token => [token])

noncomputable def identityComputableInPolyTime {Alphabet : Type}
    [Fintype Alphabet] [Inhabited Alphabet] :
    @TM2ComputableInPolyTime
      (List Alphabet) (List Alphabet) Alphabet Alphabet id id id := by
  let certificate :=
    FiniteBlockTransducer.computableInPolyTime fun item : Alphabet => [item]
  refine
    { tm := certificate.tm
      inputAlphabet := certificate.inputAlphabet
      outputAlphabet := certificate.outputAlphabet
      time := certificate.time
      outputsFun := ?_ }
  intro input
  simpa using certificate.outputsFun input

noncomputable def runAllComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (phases : List (Phase Data)) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id (runAll phases) := by
  induction phases with
  | nil =>
      exact identityComputableInPolyTime
  | cons phase phases induction =>
      let first : @TM2ComputableInPolyTime
          (List (Workspace Data)) (List (Workspace Data))
          (Workspace Data) (Workspace Data) id id phase.run :=
        phase.computableInPolyTime
      let rest : @TM2ComputableInPolyTime
          (List (Workspace Data)) (List (Workspace Data))
          (Workspace Data) (Workspace Data) id id (runAll phases) :=
        induction
      let composed := TM2CompositionMachine.computableInPolyTime first rest
      simpa only [runAll] using composed

/-- Embed once, execute every fixed affine phase, and retain only emitted
tokens. -/
noncomputable def emittedAllComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (phases : List (Phase Data)) :
    @TM2ComputableInPolyTime
      (List Data) (List Token) Data Token id id (emittedAll phases) := by
  let first := TM2CompositionMachine.computableInPolyTime
    (embedDataComputableInPolyTime (Data := Data))
    (runAllComputableInPolyTime phases)
  let complete := TM2CompositionMachine.computableInPolyTime first
    (extractTokensComputableInPolyTime (Data := Data))
  refine
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := ?_ }
  intro data
  have run := complete.outputsFun data
  have outputEq : extractTokens (runAll phases (embedData data)) =
      emittedAll phases data :=
    extractTokens_runAll_embedData phases data
  rw [outputEq] at run
  exact run

end AffineEmitterPipeline
end PeriodicCNF
end LeanTrominoes
