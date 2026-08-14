/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialStackScheduleAlgebra

/-!
# Polynomial-time complete initial-configuration emission

Assemble the exact normalized initial endpoint in finite stack order: fixed
label/control fields, empty stacks before `k₀`, the source-dependent input
stack, empty stacks after `k₀`, and the configuration-level fold closers.
The type-changing source pass occurs only at `k₀`; every other pass preserves
the shared workspace and appends tokens.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace PolySpaceInitialStackScheduleEmitter

open AffineEmitterPipeline
open AffineTemplateEmitterMachine
open BoundedMachineAtom
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceInitialSourceEmitter.Symbol
  (encoding := encoding)
abbrev InputWorkspace := PolySpaceInitialSourceEmitter.InputWorkspace
  (encoding := encoding)
abbrev Data := PolySpaceInitialSourceEmitter.Data (encoding := encoding)
abbrev Workspace := PolySpaceInitialSourceEmitter.Workspace
  (encoding := encoding)

local instance symbolInhabited : Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedSpace⟩

def prefixTokens (symbols : List encoding.Γ) : List Token :=
  ofProgram
      (BoundedMachineFixedConfigurationEmitter.labelIs (tm := decider.tm)
        .next (PolySpaceInitialEmitter.target decider symbols).l) ++
    ofProgram
      (BoundedMachineFixedConfigurationEmitter.controlIs (tm := decider.tm)
        .next (PolySpaceInitialEmitter.target decider symbols).var)

def finalTokens : List Token :=
  allEnding (Fintype.card decider.tm.K) ++
    instructionTokens .conjoin ++ instructionTokens .conjoin

def beforeTokens (symbols : List encoding.Γ) : List Token :=
  BoundedMachineEmptyStackRangeEmitter.emitted (tm := decider.tm)
    (PolySpaceInitialStackOrder.beforeInput decider)
    (PolySpaceCompiler.spaceOfSymbols decider symbols)

def afterTokens (symbols : List encoding.Γ) : List Token :=
  BoundedMachineEmptyStackRangeEmitter.emitted (tm := decider.tm)
    (PolySpaceInitialStackOrder.afterInput decider)
    (PolySpaceCompiler.spaceOfSymbols decider symbols)

def inputTailTokens (symbols : List encoding.Γ) : List Token :=
  PolySpaceInitialEmitter.emptyTailTokens decider decider.tm.k₀
    symbols.length (PolySpaceInitialTailPadding.tailCount decider symbols)

/-- One fixed token-only pass over an arbitrary affine workspace. -/
def appendTokens {Item : Type} (tokens : List Token) :
    List (AffineEmitterPipeline.Workspace Item) →
      List (AffineEmitterPipeline.Workspace Item) :=
  (BoundedMachineOneHotEmitter.fixedPhase tokens).run

theorem appendTokens_eq {Item : Type} (tokens : List Token)
    (workspace : List (AffineEmitterPipeline.Workspace Item)) :
    appendTokens tokens workspace =
      workspace ++ tokens.map fun token =>
        (Sum.inr token : AffineEmitterPipeline.Workspace Item) := by
  unfold appendTokens Phase.run BoundedMachineOneHotEmitter.fixedPhase
    AffineTemplateEmitterMachine.appendedOutput
  simp [BoundedMachineOneHotEmitter.positionRangeTokens_nil]

noncomputable def appendTokensComputableInPolyTime {Item : Type}
    [Fintype Item] [Inhabited Item] (tokens : List Token) :
    @TM2ComputableInPolyTime
      (List (AffineEmitterPipeline.Workspace Item))
      (List (AffineEmitterPipeline.Workspace Item))
      (AffineEmitterPipeline.Workspace Item)
      (AffineEmitterPipeline.Workspace Item) id id
      (appendTokens tokens) :=
  (BoundedMachineOneHotEmitter.fixedPhase tokens).computableInPolyTime

@[simp]
theorem extractTokens_map_data {Item : Type} (data : List Item) :
    AffineEmitterPipeline.extractTokens
        (data.map fun item =>
          (Sum.inl item : AffineEmitterPipeline.Workspace Item)) = [] := by
  unfold AffineEmitterPipeline.extractTokens
  rw [List.flatMap_map]
  simp

@[simp]
theorem extractTokens_map_tokens {Item : Type} (tokens : List Token) :
    AffineEmitterPipeline.extractTokens
        (tokens.map fun token =>
          (Sum.inr token : AffineEmitterPipeline.Workspace Item)) = tokens := by
  unfold AffineEmitterPipeline.extractTokens
  rw [List.flatMap_map]
  simp

@[simp]
theorem extractTokens_map_nestedLeft {First Second : Type}
    (data : List First) :
    AffineEmitterPipeline.extractTokens
        (data.map fun item =>
          (Sum.inl (Sum.inl item) :
            AffineEmitterPipeline.Workspace (First ⊕ Second))) = [] := by
  unfold AffineEmitterPipeline.extractTokens
  rw [List.flatMap_map]
  simp

@[simp]
theorem extractTokens_map_nestedRight {First Second : Type}
    (data : List Second) :
    AffineEmitterPipeline.extractTokens
        (data.map fun item =>
          (Sum.inl (Sum.inr item) :
            AffineEmitterPipeline.Workspace (First ⊕ Second))) = [] := by
  unfold AffineEmitterPipeline.extractTokens
  rw [List.flatMap_map]
  simp

@[simp]
theorem extractTokens_append {Item : Type}
    (first second : List (AffineEmitterPipeline.Workspace Item)) :
    AffineEmitterPipeline.extractTokens (first ++ second) =
      AffineEmitterPipeline.extractTokens first ++
        AffineEmitterPipeline.extractTokens second := by
  simp [AffineEmitterPipeline.extractTokens, List.flatMap_append]

def runBefore (symbols : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    List (InputWorkspace (encoding := encoding)) :=
  BoundedMachineEmptyStackRangeEmitter.run (tm := decider.tm)
    (PolySpaceInitialStackScheduleAlgebra.spaceSelectedBefore
      (encoding := encoding))
    (PolySpaceInitialStackOrder.beforeInput decider)
    (appendTokens (prefixTokens decider symbols) workspace)

theorem runBefore_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    runBefore decider symbols
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) =
      embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        (tokens ++ prefixTokens decider symbols ++ beforeTokens decider symbols).map
          (fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) := by
  unfold runBefore
  rw [appendTokens_eq,
    BoundedMachineEmptyStackRangeEmitter.run_eq_append]
  have countEq : AffineTemplateEmitterMachine.selectedCount
      (PolySpaceInitialStackScheduleAlgebra.spaceSelectedBefore
        (encoding := encoding))
      ((embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        tokens.map fun token =>
          (Sum.inr token : InputWorkspace (encoding := encoding))) ++
        (prefixTokens decider symbols).map fun token =>
          (Sum.inr token : InputWorkspace (encoding := encoding))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
    rw [AffineEmitterPipeline.selectedCount_append,
      AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero,
      PolySpaceInitialStackScheduleAlgebra.selectedCount_space_before]
  rw [countEq]
  unfold beforeTokens
  simp [List.map_append, List.append_assoc]

noncomputable def runBeforeComputableInPolyTime
    (symbols : List encoding.Γ) :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (InputWorkspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (InputWorkspace (encoding := encoding)) id id
      (runBefore decider symbols) := by
  let complete := TM2CompositionMachine.computableInPolyTime
    (appendTokensComputableInPolyTime
      (Item := Symbol (encoding := encoding)) (prefixTokens decider symbols))
    (BoundedMachineEmptyStackRangeEmitter.computableInPolyTime
      (tm := decider.tm)
      (PolySpaceInitialStackScheduleAlgebra.spaceSelectedBefore
        (encoding := encoding))
      (PolySpaceInitialStackOrder.beforeInput decider))
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (InputWorkspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (InputWorkspace (encoding := encoding)) id id
    (fun workspace =>
      BoundedMachineEmptyStackRangeEmitter.run (tm := decider.tm)
        (PolySpaceInitialStackScheduleAlgebra.spaceSelectedBefore
          (encoding := encoding))
        (PolySpaceInitialStackOrder.beforeInput decider)
        (appendTokens (prefixTokens decider symbols) workspace))
  exact complete

def runInput (symbols : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  BoundedMachineAllEndingEmitter.run
    (PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
      (encoding := encoding))
    (PolySpaceInitialTailEmitter.runWorkspace decider
      (PolySpaceInitialSourceEmitter.runWorkspace decider
        (runBefore decider symbols workspace)))

theorem runInput_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    let prior := tokens ++ prefixTokens decider symbols ++
      beforeTokens decider symbols
    let sourceWorkspace := PolySpaceInitialSourceEmitter.runWorkspace decider
      (embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        prior.map fun token =>
          (Sum.inr token : InputWorkspace (encoding := encoding)))
    runInput decider symbols
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) =
      sourceWorkspace ++
        (inputTailTokens decider symbols ++
          allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols)).map
            (fun token =>
              (Sum.inr token : Workspace (encoding := encoding))) := by
  dsimp only
  unfold runInput
  rw [runBefore_embed_append_tokens,
    PolySpaceInitialTailEmitter.runWorkspace_afterSource,
    BoundedMachineAllEndingEmitter.run_eq_append]
  have sourceCount :=
    PolySpaceInitialStackScheduleAlgebra.selectedCount_space_afterSource
      decider symbols
      (tokens ++ prefixTokens decider symbols ++ beforeTokens decider symbols)
  rw [AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero,
    sourceCount]
  unfold inputTailTokens
  simp [List.map_append, List.append_assoc]

noncomputable def runInputComputableInPolyTime
    (symbols : List encoding.Γ) :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (runInput decider symbols) := by
  let throughSource := TM2CompositionMachine.computableInPolyTime
    (runBeforeComputableInPolyTime decider symbols)
    (PolySpaceInitialSourceEmitter.runWorkspaceComputableInPolyTime decider)
  let throughTail := TM2CompositionMachine.computableInPolyTime throughSource
    (PolySpaceInitialTailEmitter.runWorkspaceComputableInPolyTime decider)
  let complete := TM2CompositionMachine.computableInPolyTime throughTail
    (BoundedMachineAllEndingEmitter.computableInPolyTime
      (PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
        (encoding := encoding)))
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (Workspace (encoding := encoding)) id id
    (fun workspace =>
      BoundedMachineAllEndingEmitter.run
        (PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
          (encoding := encoding))
        (PolySpaceInitialTailEmitter.runWorkspace decider
          (PolySpaceInitialSourceEmitter.runWorkspace decider
            (runBefore decider symbols workspace))))
  exact complete

def run (symbols : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  appendTokens (finalTokens decider)
    (BoundedMachineEmptyStackRangeEmitter.run (tm := decider.tm)
      (PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
        (encoding := encoding))
      (PolySpaceInitialStackOrder.afterInput decider)
      (runInput decider symbols workspace))

theorem run_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    let prior := tokens ++ prefixTokens decider symbols ++
      beforeTokens decider symbols
    let sourceWorkspace := PolySpaceInitialSourceEmitter.runWorkspace decider
      (embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        prior.map fun token =>
          (Sum.inr token : InputWorkspace (encoding := encoding)))
    run decider symbols
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) =
      sourceWorkspace ++
        (inputTailTokens decider symbols ++
          allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
          afterTokens decider symbols ++ finalTokens decider).map
            (fun token =>
              (Sum.inr token : Workspace (encoding := encoding))) := by
  dsimp only
  unfold run
  rw [runInput_embed_append_tokens,
    BoundedMachineEmptyStackRangeEmitter.run_eq_append,
    appendTokens_eq]
  have sourceCount :=
    PolySpaceInitialStackScheduleAlgebra.selectedCount_space_afterSource
      decider symbols
      (tokens ++ prefixTokens decider symbols ++ beforeTokens decider symbols)
  have extendedCount : AffineTemplateEmitterMachine.selectedCount
      (PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
        (encoding := encoding))
      (PolySpaceInitialSourceEmitter.runWorkspace decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            (tokens ++ prefixTokens decider symbols ++
              beforeTokens decider symbols).map fun token =>
                (Sum.inr token : InputWorkspace (encoding := encoding))) ++
        (inputTailTokens decider symbols ++
          allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols)).map
            (fun token =>
              (Sum.inr token : Workspace (encoding := encoding)))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
    rw [AffineEmitterPipeline.selectedCount_append,
      AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero, sourceCount]
  rw [extendedCount]
  unfold afterTokens
  simp [List.map_append, List.append_assoc]

/-- The component token blocks, in execution order, are exactly the exposed
normalized initial-configuration schedule. -/
theorem assembledTokens_eq_schedule (symbols : List encoding.Γ) :
    prefixTokens decider symbols ++ beforeTokens decider symbols ++
          PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
          inputTailTokens decider symbols ++
          allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
          afterTokens decider symbols ++ finalTokens decider =
      PolySpaceInitialEmitter.schedule decider symbols := by
  have stackWords :
      beforeTokens decider symbols ++
          PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
          inputTailTokens decider symbols ++
          allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
          afterTokens decider symbols =
        (finiteValues decider.tm.K).flatMap
          (PolySpaceInitialEmitter.stackSchedule decider symbols) := by
    unfold beforeTokens afterTokens inputTailTokens
    rw [PolySpaceInitialStackScheduleAlgebra.beforeEmitted_eq_stackSchedules,
      PolySpaceInitialStackScheduleAlgebra.afterEmitted_eq_stackSchedules]
    calc
      (PolySpaceInitialStackOrder.beforeInput decider).flatMap
              (PolySpaceInitialEmitter.stackSchedule decider symbols) ++
            PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
            PolySpaceInitialEmitter.emptyTailTokens decider decider.tm.k₀
              symbols.length
              (PolySpaceInitialTailPadding.tailCount decider symbols) ++
            allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
            (PolySpaceInitialStackOrder.afterInput decider).flatMap
              (PolySpaceInitialEmitter.stackSchedule decider symbols) =
          (PolySpaceInitialStackOrder.beforeInput decider).flatMap
              (PolySpaceInitialEmitter.stackSchedule decider symbols) ++
            PolySpaceInitialEmitter.stackSchedule decider symbols
              decider.tm.k₀ ++
            (PolySpaceInitialStackOrder.afterInput decider).flatMap
              (PolySpaceInitialEmitter.stackSchedule decider symbols) := by
        rw [← PolySpaceInitialStackScheduleAlgebra.inputStackWords_eq_stackSchedule]
        ac_rfl
      _ = _ :=
        (PolySpaceInitialStackOrder.flatMap_finiteValues decider
          (PolySpaceInitialEmitter.stackSchedule decider symbols)).symm
  calc
    prefixTokens decider symbols ++ beforeTokens decider symbols ++
            PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
            inputTailTokens decider symbols ++
            allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
            afterTokens decider symbols ++ finalTokens decider =
        prefixTokens decider symbols ++
          (beforeTokens decider symbols ++
            PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
            inputTailTokens decider symbols ++
            allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
            afterTokens decider symbols) ++ finalTokens decider := by
      ac_rfl
    _ = prefixTokens decider symbols ++
          (finiteValues decider.tm.K).flatMap
            (PolySpaceInitialEmitter.stackSchedule decider symbols) ++
          finalTokens decider := by rw [stackWords]
    _ = PolySpaceInitialEmitter.schedule decider symbols := by
      unfold prefixTokens finalTokens PolySpaceInitialEmitter.schedule
      ac_rfl

/-- Removing retained prepared data and unary tail markers recovers precisely
the earlier token prefix followed by the complete normalized next-initial
endpoint schedule. -/
@[simp]
theorem extractTokens_run_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineEmitterPipeline.extractTokens
        (run decider symbols
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      tokens ++ PolySpaceInitialEmitter.schedule decider symbols := by
  have extracted :
      AffineEmitterPipeline.extractTokens
          (run decider symbols
            (embedData
                (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
              tokens.map fun token =>
                (Sum.inr token : InputWorkspace (encoding := encoding)))) =
        tokens ++ prefixTokens decider symbols ++ beforeTokens decider symbols ++
          PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
          inputTailTokens decider symbols ++
          allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
          afterTokens decider symbols ++ finalTokens decider := by
    rw [run_embed_append_tokens,
      PolySpaceInitialSourceEmitter.runWorkspace_embed_append_tokens]
    simp only [extractTokens_append, extractTokens_map_nestedLeft,
      extractTokens_map_nestedRight, extractTokens_map_tokens,
      List.nil_append]
    ac_rfl
  rw [extracted]
  calc
    tokens ++ prefixTokens decider symbols ++ beforeTokens decider symbols ++
            PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
            inputTailTokens decider symbols ++
            allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
            afterTokens decider symbols ++ finalTokens decider =
        tokens ++
          (prefixTokens decider symbols ++ beforeTokens decider symbols ++
            PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
            inputTailTokens decider symbols ++
            allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
            afterTokens decider symbols ++ finalTokens decider) := by
      ac_rfl
    _ = tokens ++ PolySpaceInitialEmitter.schedule decider symbols := by
      rw [assembledTokens_eq_schedule]

noncomputable def computableInPolyTime (symbols : List encoding.Γ) :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (run decider symbols) := by
  let throughAfter := TM2CompositionMachine.computableInPolyTime
    (runInputComputableInPolyTime decider symbols)
    (BoundedMachineEmptyStackRangeEmitter.computableInPolyTime
      (tm := decider.tm)
      (PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
        (encoding := encoding))
      (PolySpaceInitialStackOrder.afterInput decider))
  let complete := TM2CompositionMachine.computableInPolyTime throughAfter
    (appendTokensComputableInPolyTime
      (Item := Data (encoding := encoding)) (finalTokens decider))
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (Workspace (encoding := encoding)) id id
    (fun workspace =>
      appendTokens (finalTokens decider)
        (BoundedMachineEmptyStackRangeEmitter.run (tm := decider.tm)
          (PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
            (encoding := encoding))
          (PolySpaceInitialStackOrder.afterInput decider)
          (runInput decider symbols workspace)))
  exact complete

end PolySpaceInitialStackScheduleEmitter
end PeriodicCNF
end LeanTrominoes
