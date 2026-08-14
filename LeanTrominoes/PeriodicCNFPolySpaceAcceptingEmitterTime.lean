/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceAcceptingEmitterSpec
import LeanTrominoes.PeriodicCNFMarkedAffineEmitterPipeline
import LeanTrominoes.SelectedPrefixMarkerTime
import LeanTrominoes.TM2CompositionMachine

/-!
# Polynomial-time accepting-configuration emission

The accepting configuration is fixed by the source decider.  First tag the
prepared unary input by its capped number of preceding space markers, then run
the already verified fixed affine phase schedule.  Their composition emits
exactly the normalized current- or next-slice accepting endpoint program in
polynomial time.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceAcceptingEmitter

open AffineEmitterPipeline
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev MarkedSymbol :=
  BoundedMachineFixedConfigurationEmitter.Marked
    (acceptingCutoff decider) (Symbol (encoding := encoding))

abbrev Workspace :=
  AffineEmitterPipeline.Workspace (Symbol (encoding := encoding))

local instance symbolInhabited :
    Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedSpace⟩

def workspaceSpace : Workspace (encoding := encoding) → Bool :=
  AffineTemplateEmitterMachine.dataSelected
    PolySpaceUnaryPreparedLayout.isSpace

def workspacePhases (slice : TransitionSlice) :
    List (Phase
      (BoundedMachineFixedConfigurationEmitter.Marked
        (acceptingCutoff decider) (Workspace (encoding := encoding)))) :=
  BoundedMachineFixedConfigurationEmitter.phases
    (tm := decider.tm) (workspaceSpace (encoding := encoding)) slice
    (PolySpaceReduction.acceptingConfiguration decider)

/-- Input-preserving accepting-endpoint pass on the shared token workspace. -/
def runWorkspace (slice : TransitionSlice)
    (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  MarkedAffineEmitterPipeline.run
    (workspaceSpace (encoding := encoding)) (acceptingCutoff decider)
    (workspacePhases decider slice) workspace

/-- The accepting pass is polynomial-time without consuming prepared data or
earlier tokens. -/
noncomputable def runWorkspaceComputableInPolyTime
    (slice : TransitionSlice) :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding)) (Workspace (encoding := encoding))
      id id (runWorkspace decider slice) :=
  MarkedAffineEmitterPipeline.computableInPolyTime
    (workspaceSpace (encoding := encoding)) (acceptingCutoff decider)
    (workspacePhases decider slice)

theorem workspaceSpace_count
    (data : List (Symbol (encoding := encoding))) (tokens : List Token) :
    UnaryPolynomialPaddingMachine.selectedCount
        (workspaceSpace (encoding := encoding))
        (embedData data ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      UnaryPolynomialPaddingMachine.selectedCount
        PolySpaceUnaryPreparedLayout.isSpace data := by
  exact selectedCount_embed_append_tokens
    PolySpaceUnaryPreparedLayout.isSpace data tokens

/-- Exact input-preserving behavior on a genuine prepared word with any
previous token prefix. -/
theorem runWorkspace_embed_append_tokens (slice : TransitionSlice)
    (symbols : List encoding.Γ) (tokens : List Token) :
    runWorkspace decider slice
        (embedData
            (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
          tokens.map fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) =
      embedData
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) ++
        (tokens ++
          ofProgram
            (BoundedMachineFixedConfigurationEmitter.configurationIs
              (tm := decider.tm) slice
              (PolySpaceReduction.acceptingConfiguration decider)
              (PolySpaceCompiler.spaceOfSymbols decider symbols))).map
          fun token =>
            (Sum.inr token : Workspace (encoding := encoding)) := by
  unfold runWorkspace
  rw [MarkedAffineEmitterPipeline.run_eq_append]
  simp only [List.map_append, ← List.append_assoc]
  congr 1
  apply congrArg (List.map fun token =>
    (Sum.inr token : Workspace (encoding := encoding)))
  apply BoundedMachineFixedConfigurationEmitter.emittedAll_phases
  · exact acceptingStackFitsCutoff decider
  · exact acceptingStackFitsSpace decider symbols
  · rw [workspaceSpace_count]
    change PolySpaceUnaryPreparedLayout.space
      (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) = _
    exact PolySpaceUnaryPreparedLayout.space_preparedSources decider symbols

/-- Mark the prepared word and emit one fixed accepting-endpoint test. -/
def emitted (slice : TransitionSlice)
    (data : List (Symbol (encoding := encoding))) : List Token :=
  emittedAll (phases decider slice)
    (mark PolySpaceUnaryPreparedLayout.isSpace
      (acceptingCutoff decider) data)

/-- The marked fixed phase schedule is a polynomial-time token emitter. -/
noncomputable def computableInPolyTime (slice : TransitionSlice) :
    @TM2ComputableInPolyTime
      (List (Symbol (encoding := encoding))) (List Token)
      (Symbol (encoding := encoding)) Token id id
      (emitted decider slice) := by
  let marker := SelectedPrefixMarkerMachine.computableInPolyTime
    (Data := Symbol (encoding := encoding))
    PolySpaceUnaryPreparedLayout.isSpace (acceptingCutoff decider)
  let printer := AffineEmitterPipeline.emittedAllComputableInPolyTime
    (phases decider slice)
  let combined := TM2CompositionMachine.computableInPolyTime marker printer
  change @TM2ComputableInPolyTime
    (List (Symbol (encoding := encoding))) (List Token)
    (Symbol (encoding := encoding)) Token id id
    (fun data => emittedAll (phases decider slice)
      (mark PolySpaceUnaryPreparedLayout.isSpace
        (acceptingCutoff decider) data))
  exact combined

/-- On actual prepared source data, the machine emits the exact normalized
accepting-configuration program at the runtime stack width. -/
theorem emitted_preparedSources (slice : TransitionSlice)
    (symbols : List encoding.Γ) :
    emitted decider slice
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      ofProgram
        (BoundedMachineFixedConfigurationEmitter.configurationIs
          (tm := decider.tm) slice
          (PolySpaceReduction.acceptingConfiguration decider)
          (PolySpaceCompiler.spaceOfSymbols decider symbols)) := by
  exact emittedAll_phases decider slice symbols

@[simp]
theorem emitted_current_preparedSources (symbols : List encoding.Γ) :
    emitted decider .current
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      ofProgram
        (BoundedMachineProgram.currentConfigIs (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (PolySpaceReduction.acceptingConfiguration decider)) := by
  simpa only [emitted] using emittedAll_currentPhases decider symbols

@[simp]
theorem emitted_next_preparedSources (symbols : List encoding.Γ) :
    emitted decider .next
        (PolySpaceUnaryPreparedLayout.preparedSources decider symbols) =
      ofProgram
        (BoundedMachineProgram.nextConfigIs (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (PolySpaceReduction.acceptingConfiguration decider)) := by
  simpa only [emitted] using emittedAll_nextPhases decider symbols

end PolySpaceAcceptingEmitter
end PeriodicCNF
end LeanTrominoes
