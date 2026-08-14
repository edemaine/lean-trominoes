/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineFixedConfigurationEmitterSpec
import LeanTrominoes.PeriodicCNFPolySpaceUnaryPreparedLayout

/-!
# Accepting-configuration emitter for the polynomial-space reduction

The designated accepting configuration is fixed by the source decider.  Its
configuration-space size is therefore a fixed prefix-marker cutoff.  This file
instantiates the generic fixed-configuration phase schedule on the concrete
four-block prepared word and proves exact emission of the current- or
next-slice accepting test at the runtime stack width.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

namespace PolySpaceAcceptingEmitter

open BoundedMachineAtom
open AffineEmitterPipeline
open UnaryProgramTokens
open SelectedPrefixMarkerMachine

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

abbrev Symbol := PolySpaceUnaryPreparedLayout.Symbol encoding

/-- Fixed tag cutoff large enough for every stack of the designated endpoint. -/
def acceptingCutoff : Nat :=
  Complexity.configurationSpace decider.tm
    (PolySpaceReduction.acceptingConfiguration decider)

theorem acceptingStackFitsCutoff (stack : decider.tm.K) :
    ((PolySpaceReduction.acceptingConfiguration decider).stk stack).length ≤
      acceptingCutoff decider := by
  exact PeriodicComputation.stack_length_le_configurationSpace decider.tm
    (PolySpaceReduction.acceptingConfiguration decider) stack

theorem acceptingStackFitsSpace (symbols : List encoding.Γ)
    (stack : decider.tm.K) :
    ((PolySpaceReduction.acceptingConfiguration decider).stk stack).length ≤
      PolySpaceCompiler.spaceOfSymbols decider symbols := by
  apply (acceptingStackFitsCutoff decider stack).trans
  unfold acceptingCutoff PolySpaceCompiler.spaceOfSymbols
  omega

/-- Fixed phase list for the accepting endpoint on either time slice. -/
def phases (slice : TransitionSlice) :
    List (Phase
      (BoundedMachineFixedConfigurationEmitter.Marked
        (acceptingCutoff decider)
        (PolySpaceUnaryPreparedLayout.Symbol encoding))) :=
  BoundedMachineFixedConfigurationEmitter.phases
    (tm := decider.tm) PolySpaceUnaryPreparedLayout.isSpace slice
    (PolySpaceReduction.acceptingConfiguration decider)

/-- The marked prepared word emits the exact accepting-configuration test. -/
theorem emittedAll_phases (slice : TransitionSlice)
    (symbols : List encoding.Γ) :
    emittedAll (phases decider slice)
        (mark PolySpaceUnaryPreparedLayout.isSpace
          (acceptingCutoff decider)
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols)) =
      ofProgram
        (BoundedMachineFixedConfigurationEmitter.configurationIs
          (tm := decider.tm) slice
          (PolySpaceReduction.acceptingConfiguration decider)
          (PolySpaceCompiler.spaceOfSymbols decider symbols)) := by
  apply BoundedMachineFixedConfigurationEmitter.emittedAll_phases
  · exact acceptingStackFitsCutoff decider
  · exact acceptingStackFitsSpace decider symbols
  · simpa [PolySpaceUnaryPreparedLayout.space] using
      PolySpaceUnaryPreparedLayout.space_preparedSources decider symbols

/-- Current-slice accepting test used by both reset and ordinary branches. -/
theorem emittedAll_currentPhases (symbols : List encoding.Γ) :
    emittedAll (phases decider .current)
        (mark PolySpaceUnaryPreparedLayout.isSpace
          (acceptingCutoff decider)
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols)) =
      ofProgram
        (BoundedMachineProgram.currentConfigIs (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (PolySpaceReduction.acceptingConfiguration decider)) := by
  simpa using emittedAll_phases decider .current symbols

/-- Next-slice accepting test, available for later endpoint compositions. -/
theorem emittedAll_nextPhases (symbols : List encoding.Γ) :
    emittedAll (phases decider .next)
        (mark PolySpaceUnaryPreparedLayout.isSpace
          (acceptingCutoff decider)
          (PolySpaceUnaryPreparedLayout.preparedSources decider symbols)) =
      ofProgram
        (BoundedMachineProgram.nextConfigIs (tm := decider.tm)
          (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
          (PolySpaceReduction.acceptingConfiguration decider)) := by
  simpa using emittedAll_phases decider .next symbols

end PolySpaceAcceptingEmitter
end PeriodicCNF
end LeanTrominoes
