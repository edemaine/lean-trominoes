/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineAllEndingEmitter

/-!
# Algebra for the complete initial stack schedule

Identify the prepared unary `space` count on both sides of the type-changing
input-stack pass.  Then connect the generic empty-stack and fold-ending words
to the exact `stackSchedule` decomposition, preserving the fixed finite stack
enumeration around `k₀`.
-/

noncomputable section

namespace LeanTrominoes

open Turing

namespace PeriodicCNF
namespace PolySpaceInitialStackScheduleAlgebra

open AffineEmitterPipeline
open AffineTemplateEmitterMachine
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

def spaceSelectedBefore : Symbol (encoding := encoding) → Bool :=
  PolySpaceUnaryPreparedLayout.isSpace

def spaceSelectedAfter : Data (encoding := encoding) → Bool
  | .inl symbol => PolySpaceUnaryPreparedLayout.isSpace symbol
  | .inr _ => false

@[simp]
theorem selectedCount_space_before (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount
        (spaceSelectedBefore (encoding := encoding))
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
  rw [AffineEmitterPipeline.selectedCount_embed_append_tokens]
  exact PolySpaceUnaryPreparedLayout.space_preparedSources decider symbols

@[simp]
theorem selectedCount_space_preparedAfter (symbols : List encoding.Γ) :
    AffineTemplateEmitterMachine.selectedCount
        (spaceSelectedAfter (encoding := encoding))
        ((PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
          (fun symbol =>
            (Sum.inl (Sum.inl symbol) : Workspace (encoding := encoding)))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
  unfold AffineTemplateEmitterMachine.selectedCount
  have mapped :
      UnaryPolynomialPaddingMachine.selectedCount
          (AffineTemplateEmitterMachine.dataSelected
            (spaceSelectedAfter (encoding := encoding)))
          ((PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
            (fun symbol =>
              (Sum.inl (Sum.inl symbol) : Workspace
                (encoding := encoding)))) =
        UnaryPolynomialPaddingMachine.selectedCount
          PolySpaceUnaryPreparedLayout.isSpace
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) := by
    induction PolySpaceUnaryPreparedLayout.preparedSources decider symbols with
    | nil => rfl
    | cons symbol symbols induction =>
        simp [AffineTemplateEmitterMachine.dataSelected, spaceSelectedAfter,
          induction]
  rw [mapped]
  exact PolySpaceUnaryPreparedLayout.space_preparedSources decider symbols

@[simp]
theorem selectedCount_space_tailMarkers (count : Nat) :
    AffineTemplateEmitterMachine.selectedCount
        (spaceSelectedAfter (encoding := encoding))
        ((List.replicate count ()).map fun marker =>
          (Sum.inl (Sum.inr marker) : Workspace (encoding := encoding))) =
      0 := by
  rw [List.map_replicate]
  unfold AffineTemplateEmitterMachine.selectedCount
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp [UnaryPolynomialPaddingMachine.selectedCount,
        AffineTemplateEmitterMachine.dataSelected, spaceSelectedAfter,
        induction]

@[simp]
theorem selectedCount_space_afterSource (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount
        (spaceSelectedAfter (encoding := encoding))
        (PolySpaceInitialSourceEmitter.runWorkspace decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
  rw [PolySpaceInitialSourceEmitter.runWorkspace_embed_append_tokens]
  simp only [AffineEmitterPipeline.selectedCount_append]
  rw [selectedCount_space_preparedAfter,
    AffineEmitterPipeline.selectedCount_map_inr,
    selectedCount_space_tailMarkers,
    AffineEmitterPipeline.selectedCount_map_inr]
  omega

/-- The generic empty-stack word is exactly the initial specification's stack
schedule for every non-input stack. -/
theorem emptyStackEmitted_eq_stackSchedule (symbols : List encoding.Γ)
    (stack : decider.tm.K) (different : stack ≠ decider.tm.k₀) :
    BoundedMachineEmptyStackEmitter.emitted (tm := decider.tm) stack
        (PolySpaceCompiler.spaceOfSymbols decider symbols) =
      PolySpaceInitialEmitter.stackSchedule decider symbols stack := by
  simp [BoundedMachineEmptyStackEmitter.emitted,
    PolySpaceInitialEmitter.stackSchedule,
    PolySpaceInitialEmitter.emptyTailTokens,
    BoundedMachineFixedConfigurationEmitter.stackPrefixTokens,
    BoundedMachineFixedConfigurationEmitter.stackCellIs,
    PolySpaceInitialEmitter.space,
    PolySpaceInitialEmitter.target_stack_other decider symbols stack
      different]

/-- The source prefix, bivariate input tail, and width-sized fold ending form
exactly the input stack's schedule. -/
theorem inputStackWords_eq_stackSchedule (symbols : List encoding.Γ) :
    PolySpaceInitialEmitter.sourcePrefixTokens decider symbols ++
        PolySpaceInitialEmitter.emptyTailTokens decider decider.tm.k₀
          symbols.length
          (PolySpaceInitialTailPadding.tailCount decider symbols) ++
        allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) =
      PolySpaceInitialEmitter.stackSchedule decider symbols decider.tm.k₀ := by
  have spaceEq := PolySpaceInitialTailPadding.space_eq_source_add_tail
    decider symbols
  have endingEq :
      allEnding (PolySpaceCompiler.spaceOfSymbols decider symbols) =
        allEnding symbols.length ++
          BoundedMachineOneHotEmitter.repeatInstructionTokens .conjoin
            (PolySpaceInitialTailPadding.tailCount decider symbols) := by
    rw [spaceEq]
    exact BoundedMachineOneHotEmitter.foldEnding_add true .conjoin
      symbols.length (PolySpaceInitialTailPadding.tailCount decider symbols)
  unfold PolySpaceInitialEmitter.stackSchedule
  rw [PolySpaceInitialEmitter.target_stack_input, List.length_map,
    PolySpaceInitialEmitter.sourcePrefixTokens_eq, endingEq]
  rw [PolySpaceInitialTailPadding.tailCount_eq_space_sub]
  unfold PolySpaceInitialEmitter.space
  dsimp only
  ac_rfl

theorem emptyRangeEmitted_eq_stackSchedules (symbols : List encoding.Γ)
    (stackList : List decider.tm.K)
    (different : ∀ stack ∈ stackList, stack ≠ decider.tm.k₀) :
    BoundedMachineEmptyStackRangeEmitter.emitted (tm := decider.tm) stackList
        (PolySpaceCompiler.spaceOfSymbols decider symbols) =
      stackList.flatMap (PolySpaceInitialEmitter.stackSchedule decider symbols) := by
  unfold BoundedMachineEmptyStackRangeEmitter.emitted
  apply List.flatMap_congr
  intro stack membership
  exact emptyStackEmitted_eq_stackSchedule decider symbols stack
    (different stack membership)

@[simp]
theorem beforeEmitted_eq_stackSchedules (symbols : List encoding.Γ) :
    BoundedMachineEmptyStackRangeEmitter.emitted (tm := decider.tm)
        (PolySpaceInitialStackOrder.beforeInput decider)
        (PolySpaceCompiler.spaceOfSymbols decider symbols) =
      (PolySpaceInitialStackOrder.beforeInput decider).flatMap
        (PolySpaceInitialEmitter.stackSchedule decider symbols) := by
  exact emptyRangeEmitted_eq_stackSchedules decider symbols _
    (PolySpaceInitialStackOrder.beforeInput_ne decider)

@[simp]
theorem afterEmitted_eq_stackSchedules (symbols : List encoding.Γ) :
    BoundedMachineEmptyStackRangeEmitter.emitted (tm := decider.tm)
        (PolySpaceInitialStackOrder.afterInput decider)
        (PolySpaceCompiler.spaceOfSymbols decider symbols) =
      (PolySpaceInitialStackOrder.afterInput decider).flatMap
        (PolySpaceInitialEmitter.stackSchedule decider symbols) := by
  exact emptyRangeEmitted_eq_stackSchedules decider symbols _
    (PolySpaceInitialStackOrder.afterInput_ne decider)

end PolySpaceInitialStackScheduleAlgebra
end PeriodicCNF
end LeanTrominoes
