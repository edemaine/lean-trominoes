/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceExpandedCounts

/-!
# Polynomial-time ordinary-branch prefix emission

After the complete reset branch, the ordinary branch starts with the negated
accepting-current test and clock succession.  Compose the expanded-workspace
emitters for these operands and stop immediately before the normalized
`machineStep` program.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceOrdinaryPrefixEmitter

open AffineEmitterPipeline
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

/-- The normalized ordinary-branch program strictly before `machineStep`. -/
def program (symbols : List encoding.Γ) : TransitionProgram.Program :=
  TransitionProgram.negate
      (BoundedMachineProgram.designatedMachineAccepts (tm := decider.tm)
        (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
        (PolySpaceReduction.acceptingConfiguration decider)) ++
    BoundedMachineProgram.clockSuccessor (tm := decider.tm)
      (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
      (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)

def prefixTokens (symbols : List encoding.Γ) : List Token :=
  ofProgram (program decider symbols)

/-- All tokens emitted through the point immediately before `machineStep`. -/
def emitted (symbols : List encoding.Γ) : List Token :=
  PolySpaceResetEmitter.emitted decider symbols ++
    prefixTokens decider symbols

/-- The remaining ordinary operands and its two conjunction closers recover
the complete normalized ordinary branch. -/
theorem ordinaryProgram_eq_prefix_step_ending (symbols : List encoding.Γ) :
    ofProgram
        (BoundedMachineProgram.designatedMachineOrdinary (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)
          (PolySpaceReduction.acceptingConfiguration decider)) =
      prefixTokens decider symbols ++
        ofProgram
          (BoundedMachineProgram.machineStep (tm := decider.tm)
            (space := PolySpaceCompiler.spaceOfSymbols decider symbols)) ++
        PolySpaceResetEmitter.branchEnding := by
  unfold BoundedMachineProgram.designatedMachineOrdinary
  unfold prefixTokens PolySpaceOrdinaryPrefixEmitter.program
    PolySpaceResetEmitter.branchEnding
  rw [ofProgram_conjoin, ofProgram_conjoin, ofProgram_append,
    ofProgram_negate]
  ac_rfl

def run (symbols : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  PolySpaceExpandedOrdinaryOperands.runClock decider
    (PolySpaceInitialStackScheduleEmitter.appendTokens
      (instructionTokens .negate)
      (PolySpaceExpandedOrdinaryOperands.runAccepting decider
        (PolySpaceResetEmitter.run decider symbols workspace)))

/-- Exact workspace behavior through the ordinary prefix. -/
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
        (prefixTokens decider symbols).map fun token =>
          (Sum.inr token : Workspace (encoding := encoding)) := by
  dsimp only
  unfold run
  let resetWorkspace :=
    PolySpaceResetEmitter.run decider symbols
      (embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        tokens.map fun token =>
          (Sum.inr token : InputWorkspace (encoding := encoding)))
  have spaceReset : AffineTemplateEmitterMachine.selectedCount
      (PolySpaceExpandedOrdinaryOperands.spaceSelected
        (encoding := encoding)) resetWorkspace =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
    exact PolySpaceExpandedCounts.selectedCount_space_reset
      decider symbols tokens
  have clockReset : AffineTemplateEmitterMachine.selectedCount
      (PolySpaceExpandedOrdinaryOperands.clockSelected
        (encoding := encoding)) resetWorkspace =
      PolySpaceCompiler.clockBitsOfSymbols decider symbols := by
    exact PolySpaceExpandedCounts.selectedCount_clock_reset
      decider symbols tokens
  rw [PolySpaceExpandedOrdinaryOperands.runAccepting_eq_append
    decider symbols resetWorkspace spaceReset,
    PolySpaceInitialStackScheduleEmitter.appendTokens_eq]
  have spaceExtended : AffineTemplateEmitterMachine.selectedCount
      (PolySpaceExpandedOrdinaryOperands.spaceSelected
        (encoding := encoding))
      ((resetWorkspace ++
          (ofProgram
            (BoundedMachineProgram.currentConfigIs (tm := decider.tm)
              (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
              (PolySpaceReduction.acceptingConfiguration decider))).map
            (fun token =>
              (Sum.inr token : Workspace (encoding := encoding)))) ++
        (instructionTokens .negate).map fun token =>
          (Sum.inr token : Workspace (encoding := encoding))) =
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
    simp only [AffineEmitterPipeline.selectedCount_append,
      AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero, spaceReset]
  have clockExtended : AffineTemplateEmitterMachine.selectedCount
      (PolySpaceExpandedOrdinaryOperands.clockSelected
        (encoding := encoding))
      ((resetWorkspace ++
          (ofProgram
            (BoundedMachineProgram.currentConfigIs (tm := decider.tm)
              (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
              (PolySpaceReduction.acceptingConfiguration decider))).map
            (fun token =>
              (Sum.inr token : Workspace (encoding := encoding)))) ++
        (instructionTokens .negate).map fun token =>
          (Sum.inr token : Workspace (encoding := encoding))) =
      PolySpaceCompiler.clockBitsOfSymbols decider symbols := by
    simp only [AffineEmitterPipeline.selectedCount_append,
      AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero, clockReset]
  rw [PolySpaceExpandedOrdinaryOperands.runClock_eq_append
    decider symbols _ spaceExtended clockExtended]
  unfold prefixTokens program BoundedMachineProgram.designatedMachineAccepts
  rw [ofProgram_append, ofProgram_negate]
  simp [List.map_append, List.append_assoc]
  dsimp only [resetWorkspace]
  rw [PolySpaceUnaryPreparedLayout.preparedSources_eq_layout]
  rfl

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
  let throughAccepting := TM2CompositionMachine.computableInPolyTime
    (PolySpaceResetEmitter.computableInPolyTime decider symbols)
    (PolySpaceExpandedOrdinaryOperands.runAcceptingComputableInPolyTime decider)
  let throughNegate := TM2CompositionMachine.computableInPolyTime
    throughAccepting
    (PolySpaceInitialStackScheduleEmitter.appendTokensComputableInPolyTime
      (Item := Data (encoding := encoding)) (instructionTokens .negate))
  let complete := TM2CompositionMachine.computableInPolyTime throughNegate
    (PolySpaceExpandedOrdinaryOperands.runClockComputableInPolyTime decider)
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (Workspace (encoding := encoding)) id id
    (fun workspace =>
      PolySpaceExpandedOrdinaryOperands.runClock decider
        (PolySpaceInitialStackScheduleEmitter.appendTokens
          (instructionTokens .negate)
          (PolySpaceExpandedOrdinaryOperands.runAccepting decider
            (PolySpaceResetEmitter.run decider symbols workspace))))
  exact complete

end PolySpaceOrdinaryPrefixEmitter
end PeriodicCNF
end LeanTrominoes
