/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceExpandedOrdinaryOperands

/-!
# Selected counts after normalized reset emission

The initial-stack pass changes the stable data alphabet by adjoining unary
input-tail markers.  This file records the exact reset-workspace shape and
proves that the lifted space and clock selectors still recover the two widths
of the prepared source.  These are precisely the hypotheses needed by the
ordinary-branch accepting and clock-successor emitters.
-/

noncomputable section

namespace LeanTrominoes

open Turing

namespace PeriodicCNF
namespace PolySpaceExpandedCounts

open AffineEmitterPipeline
open UnaryProgramTokens

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

def priorTokens (symbols : List encoding.Γ) (tokens : List Token) :
    List Token :=
  tokens ++ PolySpaceResetPrefixEmitter.emitted decider symbols ++
    PolySpaceInitialStackScheduleEmitter.prefixTokens decider symbols ++
    PolySpaceInitialStackScheduleEmitter.beforeTokens decider symbols

def sourceWorkspace (symbols : List encoding.Γ) (tokens : List Token) :
    List (Workspace (encoding := encoding)) :=
  PolySpaceInitialSourceEmitter.runWorkspace decider
    (embedData
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
      (priorTokens decider symbols tokens).map fun token =>
        (Sum.inr token : InputWorkspace (encoding := encoding)))

def remainingTokens (symbols : List encoding.Γ) : List Token :=
  PolySpaceInitialStackScheduleEmitter.inputTailTokens decider symbols ++
    UnaryProgramTokenAlgebra.allEnding
      (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
    PolySpaceInitialStackScheduleEmitter.afterTokens decider symbols ++
    PolySpaceInitialStackScheduleEmitter.finalTokens decider ++
    PolySpaceResetEmitter.branchEnding

/-- Exact stable workspace after the complete reset-prefix pass. -/
theorem reset_run_eq_source_append (symbols : List encoding.Γ)
    (tokens : List Token) :
    PolySpaceResetEmitter.run decider symbols
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) =
      sourceWorkspace decider symbols tokens ++
        (remainingTokens decider symbols).map fun token =>
          (Sum.inr token : Workspace (encoding := encoding)) := by
  unfold PolySpaceResetEmitter.run
  rw [PolySpaceResetPrefixEmitter.runWorkspace_embed_append_tokens,
    PolySpaceInitialStackScheduleEmitter.run_embed_append_tokens,
    PolySpaceInitialStackScheduleEmitter.appendTokens_eq]
  simp [sourceWorkspace, priorTokens, remainingTokens, List.map_append,
    List.append_assoc]

@[simp]
theorem selectedCount_clock_preparedAfter (symbols : List encoding.Γ) :
    AffineTemplateEmitterMachine.selectedCount
        (PolySpaceExpandedOrdinaryOperands.clockSelected
          (encoding := encoding))
        ((PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
          (fun symbol =>
            (Sum.inl (Sum.inl symbol) : Workspace
              (encoding := encoding)))) =
      PolySpaceCompiler.clockBitsOfSymbols decider symbols := by
  unfold AffineTemplateEmitterMachine.selectedCount
  have mapped :
      UnaryPolynomialPaddingMachine.selectedCount
          (AffineTemplateEmitterMachine.dataSelected
            (PolySpaceExpandedOrdinaryOperands.clockSelected
              (encoding := encoding)))
          ((PolySpaceUnaryPreparedLayout.preparedSources decider symbols).map
            (fun symbol =>
              (Sum.inl (Sum.inl symbol) : Workspace
                (encoding := encoding)))) =
        UnaryPolynomialPaddingMachine.selectedCount
          PolySpaceUnaryPreparedLayout.isClock
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) := by
    induction PolySpaceUnaryPreparedLayout.preparedSources decider symbols with
    | nil => rfl
    | cons symbol symbols induction =>
        simp [AffineTemplateEmitterMachine.dataSelected,
          PolySpaceExpandedOrdinaryOperands.clockSelected, induction]
  rw [mapped]
  exact PolySpaceUnaryPreparedLayout.clockWidth_preparedSources decider symbols

@[simp]
theorem selectedCount_clock_tailMarkers (count : Nat) :
    AffineTemplateEmitterMachine.selectedCount
        (PolySpaceExpandedOrdinaryOperands.clockSelected
          (encoding := encoding))
        ((List.replicate count ()).map fun marker =>
          (Sum.inl (Sum.inr marker) : Workspace
            (encoding := encoding))) = 0 := by
  rw [List.map_replicate]
  unfold AffineTemplateEmitterMachine.selectedCount
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ]
      simp [UnaryPolynomialPaddingMachine.selectedCount,
        AffineTemplateEmitterMachine.dataSelected,
        PolySpaceExpandedOrdinaryOperands.clockSelected, induction]

@[simp]
theorem selectedCount_clock_afterSource (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount
        (PolySpaceExpandedOrdinaryOperands.clockSelected
          (encoding := encoding))
        (PolySpaceInitialSourceEmitter.runWorkspace decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      PolySpaceCompiler.clockBitsOfSymbols decider symbols := by
  rw [PolySpaceInitialSourceEmitter.runWorkspace_embed_append_tokens]
  simp only [AffineEmitterPipeline.selectedCount_append]
  rw [selectedCount_clock_preparedAfter,
    AffineEmitterPipeline.selectedCount_map_inr,
    selectedCount_clock_tailMarkers,
    AffineEmitterPipeline.selectedCount_map_inr]
  omega

/-- Reset emission preserves the exact expanded-workspace stack width. -/
@[simp]
theorem selectedCount_space_reset (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount
        (PolySpaceExpandedOrdinaryOperands.spaceSelected
          (encoding := encoding))
        (PolySpaceResetEmitter.run decider symbols
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
  rw [reset_run_eq_source_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
  exact
    PolySpaceInitialStackScheduleAlgebra.selectedCount_space_afterSource
      decider symbols (priorTokens decider symbols tokens)

/-- Reset emission preserves the exact expanded-workspace clock width. -/
@[simp]
theorem selectedCount_clock_reset (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount
        (PolySpaceExpandedOrdinaryOperands.clockSelected
          (encoding := encoding))
        (PolySpaceResetEmitter.run decider symbols
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      PolySpaceCompiler.clockBitsOfSymbols decider symbols := by
  rw [reset_run_eq_source_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
  exact selectedCount_clock_afterSource decider symbols
    (priorTokens decider symbols tokens)

end PolySpaceExpandedCounts
end PeriodicCNF
end LeanTrominoes
