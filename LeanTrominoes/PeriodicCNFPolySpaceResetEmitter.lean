/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialStackScheduleEmitter

/-!
# Polynomial-time complete designated reset-branch emission

Compose structural well-formedness, the current accepting endpoint, clock
reset, and the source-dependent next-initial endpoint.  Two final conjunction
instructions close the exact normalized designated reset branch.  The result
is the complete program prefix immediately before the ordinary branch.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceResetEmitter

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

/-- Operators closing `clockReset ∧ nextInitial` and then
`acceptingCurrent ∧ (...)`. -/
def branchEnding : List Token :=
  instructionTokens .conjoin ++ instructionTokens .conjoin

/-- Exact token prefix consisting of well-formedness and the complete reset
branch, but not yet the ordinary branch or the outer disjunction/conjunction. -/
def emitted (symbols : List encoding.Γ) : List Token :=
  ofProgram
      (BoundedMachineProgram.wellFormedFields (tm := decider.tm)
        (space := PolySpaceCompiler.spaceOfSymbols decider symbols)) ++
    ofProgram
      (BoundedMachineProgram.designatedMachineReset (tm := decider.tm)
        (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
        (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)
        (PolySpaceInitialEmitter.target decider symbols)
        (PolySpaceReduction.acceptingConfiguration decider))

theorem emitted_eq_components (symbols : List encoding.Γ) :
    emitted decider symbols =
      PolySpaceResetPrefixEmitter.emitted decider symbols ++
        PolySpaceInitialEmitter.schedule decider symbols ++ branchEnding := by
  unfold emitted PolySpaceResetPrefixEmitter.emitted
    PolySpaceResetPrefixEmitter.program branchEnding
    BoundedMachineProgram.designatedMachineReset
    BoundedMachineProgram.designatedMachineAccepts
  rw [ofProgram_conjoin, ofProgram_conjoin]
  simp only [PolySpaceInitialEmitter.schedule_eq]
  simp only [ofProgram_append]
  ac_rfl

def run (symbols : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  PolySpaceInitialStackScheduleEmitter.appendTokens branchEnding
    (PolySpaceInitialStackScheduleEmitter.run decider symbols
      (PolySpaceResetPrefixEmitter.runWorkspace decider workspace))

noncomputable def computableInPolyTime (symbols : List encoding.Γ) :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (run decider symbols) := by
  let throughInitial := TM2CompositionMachine.computableInPolyTime
    (PolySpaceResetPrefixEmitter.runWorkspaceComputableInPolyTime decider)
    (PolySpaceInitialStackScheduleEmitter.computableInPolyTime decider symbols)
  let complete := TM2CompositionMachine.computableInPolyTime throughInitial
    (PolySpaceInitialStackScheduleEmitter.appendTokensComputableInPolyTime
      (Item := Data (encoding := encoding)) branchEnding)
  change @TM2ComputableInPolyTime
    (List (InputWorkspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (InputWorkspace (encoding := encoding))
    (Workspace (encoding := encoding)) id id
    (fun workspace =>
      PolySpaceInitialStackScheduleEmitter.appendTokens branchEnding
        (PolySpaceInitialStackScheduleEmitter.run decider symbols
          (PolySpaceResetPrefixEmitter.runWorkspace decider workspace)))
  exact complete

/-- One fixed reset-branch emitter for all prepared source words. -/
def uniformRun
    (workspace : List (InputWorkspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  PolySpaceInitialStackScheduleEmitter.appendTokens branchEnding
    (PolySpaceInitialStackScheduleEmitter.uniformRun decider
      (PolySpaceResetPrefixEmitter.runWorkspace decider workspace))

theorem uniformRun_eq_run (symbols : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    uniformRun decider workspace = run decider symbols workspace := by
  unfold uniformRun run
  rw [PolySpaceInitialStackScheduleEmitter.uniformRun_eq_run decider symbols]

theorem run_source_independent (first second : List encoding.Γ)
    (workspace : List (InputWorkspace (encoding := encoding))) :
    run decider first workspace = run decider second workspace := by
  rw [← uniformRun_eq_run decider first,
    ← uniformRun_eq_run decider second]

noncomputable def uniformComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (InputWorkspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (InputWorkspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (uniformRun decider) := by
  let throughInitial := TM2CompositionMachine.computableInPolyTime
    (PolySpaceResetPrefixEmitter.runWorkspaceComputableInPolyTime decider)
    (PolySpaceInitialStackScheduleEmitter.uniformComputableInPolyTime decider)
  let complete := TM2CompositionMachine.computableInPolyTime throughInitial
    (PolySpaceInitialStackScheduleEmitter.appendTokensComputableInPolyTime
      (Item := Data (encoding := encoding)) branchEnding)
  exact complete

/-- The complete pass preserves any earlier token prefix and appends exactly
well-formedness followed by the designated reset branch. -/
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
  unfold run
  rw [PolySpaceResetPrefixEmitter.runWorkspace_embed_append_tokens,
    PolySpaceInitialStackScheduleEmitter.appendTokens_eq,
    PolySpaceInitialStackScheduleEmitter.extractTokens_append,
    PolySpaceInitialStackScheduleEmitter.extractTokens_map_tokens,
    PolySpaceInitialStackScheduleEmitter.extractTokens_run_embed_append_tokens,
    emitted_eq_components]
  ac_rfl

@[simp]
theorem extractTokens_uniformRun_embed_append_tokens
    (symbols : List encoding.Γ) (tokens : List Token) :
    AffineEmitterPipeline.extractTokens
        (uniformRun decider
          (embedData
              (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
            tokens.map fun token =>
              (Sum.inr token : InputWorkspace (encoding := encoding)))) =
      tokens ++ emitted decider symbols := by
  rw [uniformRun_eq_run decider symbols,
    extractTokens_run_embed_append_tokens]

end PolySpaceResetEmitter
end PeriodicCNF
end LeanTrominoes
