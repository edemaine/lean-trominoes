/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceAcceptingEmitterTime
import LeanTrominoes.PeriodicCNFPolySpaceClockResetEmitterSpec
import LeanTrominoes.PeriodicCNFPolySpaceWellFormedEmitterSpec

/-!
# Polynomial-time reset-branch request prefix

The normalized designated reset-clock program begins with structural
well-formedness, the current accepting-endpoint test, and the clock-reset
operands.  These three input-preserving passes are composed here.  The next
token required after this prefix belongs to the source-dependent initial
configuration emitter.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceResetPrefixEmitter

open AffineEmitterPipeline
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding
abbrev Workspace := AffineEmitterPipeline.Workspace
  (Symbol (encoding := encoding))

/-- Exact normalized instruction prefix before the next-initial endpoint. -/
def program (symbols : List encoding.Γ) : TransitionProgram.Program :=
  BoundedMachineProgram.wellFormedFields (tm := decider.tm)
      (space := PolySpaceCompiler.spaceOfSymbols decider symbols) ++
    BoundedMachineProgram.currentConfigIs (tm := decider.tm)
      (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
      (PolySpaceReduction.acceptingConfiguration decider) ++
    BoundedMachineProgram.clockReset (tm := decider.tm)
      (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
      (clockBits := PolySpaceCompiler.clockBitsOfSymbols decider symbols)

def emitted (symbols : List encoding.Γ) : List Token :=
  ofProgram (program decider symbols)

/-- Compose the three shared-workspace passes in normalized postorder. -/
def runWorkspace (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  PolySpaceClockResetEmitter.runWorkspace decider
    (PolySpaceAcceptingEmitter.runWorkspace decider .current
      (PolySpaceWellFormedEmitter.runWorkspace decider workspace))

noncomputable def runWorkspaceComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding)) (Workspace (encoding := encoding))
      id id (runWorkspace decider) := by
  let first := TM2CompositionMachine.computableInPolyTime
    (PolySpaceWellFormedEmitter.runWorkspaceComputableInPolyTime decider)
    (PolySpaceAcceptingEmitter.runWorkspaceComputableInPolyTime
      decider .current)
  let complete := TM2CompositionMachine.computableInPolyTime first
    (PolySpaceClockResetEmitter.runWorkspaceComputableInPolyTime decider)
  change @TM2ComputableInPolyTime
    (List (Workspace (encoding := encoding)))
    (List (Workspace (encoding := encoding)))
    (Workspace (encoding := encoding)) (Workspace (encoding := encoding))
    id id
    (fun workspace =>
      PolySpaceClockResetEmitter.runWorkspace decider
        (PolySpaceAcceptingEmitter.runWorkspace decider .current
          (PolySpaceWellFormedEmitter.runWorkspace decider workspace)))
  exact complete

/-- Exact prefix behavior after any previously emitted token word. -/
theorem runWorkspace_embed_append_tokens (symbols : List encoding.Γ)
    (tokens : List Token) :
    runWorkspace decider
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        (tokens ++ emitted decider symbols).map fun token =>
          (Sum.inr token : Workspace (encoding := encoding)) := by
  unfold runWorkspace
  rw [PolySpaceWellFormedEmitter.runWorkspace_embed_append_tokens]
  rw [PolySpaceAcceptingEmitter.runWorkspace_embed_append_tokens]
  rw [PolySpaceClockResetEmitter.runWorkspace_embed_append_tokens]
  rw [PolySpaceClockResetEmitter.emitted_preparedSources]
  simp only [BoundedMachineFixedConfigurationEmitter.configurationIs_current]
  unfold emitted program
  simp [ofProgram, List.map_append, List.append_assoc]

end PolySpaceResetPrefixEmitter
end PeriodicCNF
end LeanTrominoes
