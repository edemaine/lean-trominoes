/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceOrdinaryPrefixEmitter
import LeanTrominoes.PeriodicCNFMachineStepEmitter

/-!
# Complete polynomial-space ordinary-branch emission

Append the exact runtime `machineStep` program and the two fixed conjunction
closers to the existing ordinary prefix.  The result is the complete
normalized ordinary branch after the complete reset branch.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceOrdinaryEmitter

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

def ordinaryTokens (symbols : List encoding.Γ) : List Token :=
  PolySpaceOrdinaryPrefixEmitter.prefixTokens decider symbols ++
    BoundedMachineStepEmitter.emitted (tm := decider.tm)
      (PolySpaceCompiler.spaceOfSymbols decider symbols) ++
    PolySpaceResetEmitter.branchEnding

def emitted (symbols : List encoding.Γ) : List Token :=
  PolySpaceResetEmitter.emitted decider symbols ++ ordinaryTokens decider symbols

def run (symbols : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  PolySpaceInitialStackScheduleEmitter.appendTokens
    PolySpaceResetEmitter.branchEnding
    (BoundedMachineStepEmitter.run (tm := decider.tm)
      (PolySpaceExpandedOrdinaryOperands.spaceSelected (encoding := encoding))
      (PolySpaceOrdinaryPrefixEmitter.run decider symbols workspace))

theorem selectedCount_space_prefix (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineTemplateEmitterMachine.selectedCount
        (PolySpaceExpandedOrdinaryOperands.spaceSelected
          (encoding := encoding))
        (PolySpaceOrdinaryPrefixEmitter.run decider symbols
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
  rw [PolySpaceOrdinaryPrefixEmitter.run_eq_reset_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
  exact PolySpaceExpandedCounts.selectedCount_space_reset
    decider symbols tokens

/-- Exact workspace behavior through the complete ordinary branch. -/
theorem run_eq_reset_append (symbols : List encoding.Γ)
    (tokens : List Token) :
    let resetWorkspace :=
      PolySpaceResetEmitter.run decider symbols
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding)))
    run decider symbols
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : InputWorkspace (encoding := encoding))) =
      resetWorkspace ++
        (ordinaryTokens decider symbols).map fun token =>
          (Sum.inr token : Workspace (encoding := encoding)) := by
  dsimp only
  unfold run
  rw [PolySpaceInitialStackScheduleEmitter.appendTokens_eq,
    BoundedMachineStepEmitter.run_eq_append,
    selectedCount_space_prefix,
    PolySpaceOrdinaryPrefixEmitter.run_eq_reset_append]
  unfold ordinaryTokens
  simp [List.map_append, List.append_assoc]

@[simp]
theorem extractTokens_run_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    AffineEmitterPipeline.extractTokens
        (run decider symbols
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      tokens ++ emitted decider symbols := by
  rw [run_eq_reset_append,
    PolySpaceInitialStackScheduleEmitter.extractTokens_append,
    PolySpaceInitialStackScheduleEmitter.extractTokens_map_tokens,
    PolySpaceResetEmitter.extractTokens_run_embed_append_tokens]
  unfold emitted
  ac_rfl

noncomputable def computableInPolyTime (symbols : List encoding.Γ) :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (run decider symbols) := by
  let throughStep := TM2CompositionMachine.computableInPolyTime
    (PolySpaceOrdinaryPrefixEmitter.computableInPolyTime decider symbols)
    (BoundedMachineStepEmitter.computableInPolyTime (tm := decider.tm)
      (PolySpaceExpandedOrdinaryOperands.spaceSelected
        (encoding := encoding)))
  let complete := TM2CompositionMachine.computableInPolyTime throughStep
    (PolySpaceInitialStackScheduleEmitter.appendTokensComputableInPolyTime
      (Item := Data (encoding := encoding))
      PolySpaceResetEmitter.branchEnding)
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (Workspace (encoding := encoding)) id id
    (fun workspace =>
      PolySpaceInitialStackScheduleEmitter.appendTokens
        PolySpaceResetEmitter.branchEnding
        (BoundedMachineStepEmitter.run (tm := decider.tm)
          (PolySpaceExpandedOrdinaryOperands.spaceSelected
            (encoding := encoding))
          (PolySpaceOrdinaryPrefixEmitter.run decider symbols workspace)))
  exact complete

/-- The emitted ordinary suffix is exactly the normalized ordinary branch. -/
theorem ordinaryTokens_eq_program (symbols : List encoding.Γ) :
    ordinaryTokens decider symbols =
      ofProgram
        (BoundedMachineProgram.designatedMachineOrdinary (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)
          (PolySpaceReduction.acceptingConfiguration decider)) := by
  unfold ordinaryTokens
  rw [BoundedMachineStepEmitter.emitted_eq_machineStep]
  exact (PolySpaceOrdinaryPrefixEmitter.ordinaryProgram_eq_prefix_step_ending
    decider symbols).symm

end PolySpaceOrdinaryEmitter
end PeriodicCNF
end LeanTrominoes
