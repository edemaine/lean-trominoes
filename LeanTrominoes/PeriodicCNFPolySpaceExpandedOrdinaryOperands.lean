/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceResetEmitter
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterTime

/-!
# Accepting and clock-successor operands on the expanded workspace

After next-initial emission, the stable data alphabet contains original
prepared symbols plus unary input-tail markers.  Lift the prepared space and
clock selectors through that sum, and specialize the existing marked affine
and triangular machines to this expanded workspace.  Their exact behavior
depends only on the two preserved selected counts.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace PolySpaceExpandedOrdinaryOperands

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
abbrev Data := PolySpaceInitialSourceEmitter.Data (encoding := encoding)
abbrev Workspace := PolySpaceInitialSourceEmitter.Workspace
  (encoding := encoding)

local instance symbolInhabited : Inhabited (Symbol (encoding := encoding)) :=
  ⟨PolySpaceUnaryPreparedLayout.embedSpace⟩

def spaceSelected : Data (encoding := encoding) → Bool :=
  PolySpaceInitialStackScheduleAlgebra.spaceSelectedAfter
    (encoding := encoding)

def clockSelected : Data (encoding := encoding) → Bool
  | .inl symbol => PolySpaceUnaryPreparedLayout.isClock symbol
  | .inr _ => false

def workspaceSpace : Workspace (encoding := encoding) → Bool :=
  AffineTemplateEmitterMachine.dataSelected
    (spaceSelected (encoding := encoding))

abbrev MarkedWorkspace :=
  BoundedMachineFixedConfigurationEmitter.Marked
    (PolySpaceAcceptingEmitter.acceptingCutoff decider)
    (Workspace (encoding := encoding))

def acceptingPhases :
    List (AffineEmitterPipeline.Phase
      (BoundedMachineFixedConfigurationEmitter.Marked
        (PolySpaceAcceptingEmitter.acceptingCutoff decider)
        (Workspace (encoding := encoding)))) :=
  BoundedMachineFixedConfigurationEmitter.phases
    (tm := decider.tm) (workspaceSpace (encoding := encoding)) .current
    (PolySpaceReduction.acceptingConfiguration decider)

def runAccepting (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  MarkedAffineEmitterPipeline.run
    (workspaceSpace (encoding := encoding))
    (PolySpaceAcceptingEmitter.acceptingCutoff decider)
    (acceptingPhases decider) workspace

noncomputable def runAcceptingComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (runAccepting decider) :=
  MarkedAffineEmitterPipeline.computableInPolyTime
    (workspaceSpace (encoding := encoding))
    (PolySpaceAcceptingEmitter.acceptingCutoff decider)
    (acceptingPhases decider)

/-- Exact accepting-current suffix on any expanded workspace with the right
selected stack width. -/
theorem runAccepting_eq_append (symbols : List encoding.Γ)
    (workspace : List (Workspace (encoding := encoding)))
    (spaceEq : AffineTemplateEmitterMachine.selectedCount
      (spaceSelected (encoding := encoding)) workspace =
        PolySpaceCompiler.spaceOfSymbols decider symbols) :
    runAccepting decider workspace =
      workspace ++
        (ofProgram
          (BoundedMachineProgram.currentConfigIs (tm := decider.tm)
            (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
            (PolySpaceReduction.acceptingConfiguration decider))).map
          (fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) := by
  unfold runAccepting
  rw [MarkedAffineEmitterPipeline.run_eq_append]
  congr 1
  apply congrArg (List.map fun token =>
    (Sum.inr token : Workspace (encoding := encoding)))
  apply BoundedMachineFixedConfigurationEmitter.emittedAll_currentPhases
  · exact PolySpaceAcceptingEmitter.acceptingStackFitsCutoff decider
  · exact PolySpaceAcceptingEmitter.acceptingStackFitsSpace decider symbols
  · change AffineTemplateEmitterMachine.selectedCount
      (spaceSelected (encoding := encoding)) workspace = _
    exact spaceEq

def clockParameters : TriangularTemplateEmitterMachine.Parameters
    (Data (encoding := encoding)) where
  firstSelected := spaceSelected (encoding := encoding)
  secondSelected := clockSelected (encoding := encoding)
  outerFirst :=
    (BoundedMachineBivariateClockSuccessor.rise (tm := decider.tm)).recipes
  inner :=
    (BoundedMachineBivariateClockSuccessor.equalBit
      (tm := decider.tm)).recipes
  outerSecond :=
    (BoundedMachineBivariateClockSuccessor.fall (tm := decider.tm)).recipes
  innerBase := ofProgram (TransitionProgram.constant true)
  innerCloser := ofProgram [.conjoin]
  frameCloser := ofProgram [.conjoin]
  finalBase := ofProgram (TransitionProgram.constant false)
  finalCloser := ofProgram [.conjoin, .disjoin]

def runClock (workspace : List (Workspace (encoding := encoding))) :
    List (Workspace (encoding := encoding)) :=
  TriangularTemplateEmitterMachine.appendedOutput
    (clockParameters decider).firstSelected
    (clockParameters decider).secondSelected
    (clockParameters decider).outerFirst (clockParameters decider).inner
    (clockParameters decider).outerSecond
    (clockParameters decider).innerBase
    (clockParameters decider).innerCloser
    (clockParameters decider).frameCloser
    (clockParameters decider).finalBase
    (clockParameters decider).finalCloser workspace

noncomputable def runClockComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List (Workspace (encoding := encoding)))
      (List (Workspace (encoding := encoding)))
      (Workspace (encoding := encoding))
      (Workspace (encoding := encoding)) id id
      (runClock decider) :=
  TriangularTemplateEmitterMachine.computableInPolyTime
    (clockParameters decider)

/-- Exact clock-successor suffix on any expanded workspace with the right
space and clock selected counts. -/
theorem runClock_eq_append (symbols : List encoding.Γ)
    (workspace : List (Workspace (encoding := encoding)))
    (spaceEq : AffineTemplateEmitterMachine.selectedCount
      (spaceSelected (encoding := encoding)) workspace =
        PolySpaceCompiler.spaceOfSymbols decider symbols)
    (clockEq : AffineTemplateEmitterMachine.selectedCount
      (clockSelected (encoding := encoding)) workspace =
        PolySpaceCompiler.clockBitsOfSymbols decider symbols) :
    runClock decider workspace =
      workspace ++
        (ofProgram
          (BoundedMachineProgram.clockSuccessor (tm := decider.tm)
            (space := PolySpaceCompiler.spaceOfSymbols decider symbols)
            (clockBits :=
              PolySpaceCompiler.clockBitsOfSymbols decider symbols))).map
          (fun token =>
            (Sum.inr token : Workspace (encoding := encoding))) := by
  unfold runClock TriangularTemplateEmitterMachine.appendedOutput
  change workspace ++
      (TriangularTemplateEmitter.emitted
        (BoundedMachineBivariateClockSuccessor.rise
          (tm := decider.tm)).recipes
        (BoundedMachineBivariateClockSuccessor.equalBit
          (tm := decider.tm)).recipes
        (BoundedMachineBivariateClockSuccessor.fall
          (tm := decider.tm)).recipes
        (ofProgram (TransitionProgram.constant true))
        (ofProgram [.conjoin]) (ofProgram [.conjoin])
        (ofProgram (TransitionProgram.constant false))
        (ofProgram [.conjoin, .disjoin])
        (AffineTemplateEmitterMachine.selectedCount
          (spaceSelected (encoding := encoding)) workspace)
        (AffineTemplateEmitterMachine.selectedCount
          (clockSelected (encoding := encoding)) workspace)).map Sum.inr = _
  rw [spaceEq, clockEq,
    TriangularTemplateEmitter.emitted_clockSuccessor,
    BoundedMachineBivariateClockSuccessor.clockSuccessorTokens_eq]

end PolySpaceExpandedOrdinaryOperands
end PeriodicCNF
end LeanTrominoes
