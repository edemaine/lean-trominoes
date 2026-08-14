/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceAcceptingEmitterSpec
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

local instance symbolInhabited :
    Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedSpace⟩

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
