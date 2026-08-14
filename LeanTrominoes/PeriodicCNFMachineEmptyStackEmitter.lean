/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialTailEmitter
import LeanTrominoes.PeriodicCNFMachineOneHotEmitterSpec

/-!
# Polynomial-time emission of one empty bounded stack

An empty stack of runtime width `n` consists of `n` affine `none`-cell tests,
the constant-true base of `TransitionProgram.all`, and `n` conjunction
closers.  Two ordinary affine passes emit this exact normalized word while
preserving an arbitrary shared data/token workspace.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineEmptyStackEmitter

open AffineEmitterPipeline
open AffineProgramTemplates
open AffineTemplateEmitterMachine
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def cellPhase {Data : Type} (selected : Data → Bool)
    (stack : tm.K) : Phase Data where
  selected := selected
  recipes :=
    (BoundedMachineAffineProgram.nextStackCellIs (tm := tm)
      stack 0 none).recipes
  ending := allEnding 0

def closerPhase {Data : Type} (selected : Data → Bool) : Phase Data where
  selected := selected
  recipes := AffineProgramTemplates.Program.recipes
    ([.conjoin] : AffineProgramTemplates.Program)
  ending := []

def phases {Data : Type} (selected : Data → Bool)
    (stack : tm.K) : List (Phase Data) :=
  [cellPhase (tm := tm) selected stack, closerPhase selected]

/-- Exact token schedule for an empty stack of the supplied width. -/
def emitted (stack : tm.K) (count : Nat) : List Token :=
  ((List.range count).flatMap fun position =>
      ofProgram
        (BoundedMachineFixedConfigurationEmitter.stackCellIs
          (tm := tm) .next stack position none)) ++
    allEnding 0 ++
    BoundedMachineOneHotEmitter.repeatInstructionTokens .conjoin count

theorem cellRange_eq (stack : tm.K) (count : Nat) :
    positionRangeTokens
        (BoundedMachineAffineProgram.nextStackCellIs (tm := tm)
          stack 0 none).recipes 0 count =
      (List.range count).flatMap fun position =>
        ofProgram
          (BoundedMachineFixedConfigurationEmitter.stackCellIs
            (tm := tm) .next stack position none) := by
  rw [UnaryProgramTokenAlgebra.positionRangeTokens_program,
    BoundedMachineOneHotEmitter.positions_zero_eq_range]
  apply List.flatMap_congr
  intro position _
  rw [BoundedMachineAffineProgram.evaluate_nextStackCellIs]
  simp [BoundedMachineFixedConfigurationEmitter.stackCellIs]

theorem closerRange_eq (count : Nat) :
    positionRangeTokens
        (AffineProgramTemplates.Program.recipes
          ([.conjoin] : AffineProgramTemplates.Program)) 0 count =
      BoundedMachineOneHotEmitter.repeatInstructionTokens .conjoin count := by
  rw [UnaryProgramTokenAlgebra.positionRangeTokens_program]
  simp only [AffineProgramTemplates.Program.evaluate]
  exact BoundedMachineOneHotEmitter.flatMap_positions_constant .conjoin count

def run {Data : Type} (selected : Data → Bool) (stack : tm.K) :
    List (AffineEmitterPipeline.Workspace Data) →
      List (AffineEmitterPipeline.Workspace Data) :=
  runAll (phases (tm := tm) selected stack)

/-- Both passes preserve the entire incoming workspace and append precisely
the normalized empty-stack word at the selected width. -/
theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (stack : tm.K)
    (workspace : List (AffineEmitterPipeline.Workspace Data)) :
    run (tm := tm) selected stack workspace =
      workspace ++
        (emitted (tm := tm) stack
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token =>
              (Sum.inr token : AffineEmitterPipeline.Workspace Data) := by
  let count := AffineTemplateEmitterMachine.selectedCount selected workspace
  let cells := positionRangeTokens
    (BoundedMachineAffineProgram.nextStackCellIs (tm := tm)
      stack 0 none).recipes 0 count ++ allEnding 0
  have selectedAfterCells :
      AffineTemplateEmitterMachine.selectedCount selected
          (workspace ++ cells.map fun token =>
            (Sum.inr token : AffineEmitterPipeline.Workspace Data)) = count := by
    rw [AffineEmitterPipeline.selectedCount_append,
      AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
  unfold run phases
  simp only [runAll]
  unfold Phase.run cellPhase closerPhase
    AffineTemplateEmitterMachine.appendedOutput
  simp only [List.append_nil]
  change (workspace ++ cells.map fun token =>
      (Sum.inr token : AffineEmitterPipeline.Workspace Data)) ++
        (positionRangeTokens
          (AffineProgramTemplates.Program.recipes
            ([.conjoin] : AffineProgramTemplates.Program)) 0
          (AffineTemplateEmitterMachine.selectedCount selected
            (workspace ++ cells.map fun token =>
              (Sum.inr token :
                AffineEmitterPipeline.Workspace Data)))).map Sum.inr = _
  rw [selectedAfterCells]
  unfold cells count
  rw [cellRange_eq, closerRange_eq]
  unfold emitted
  simp [List.map_append, List.append_assoc]

/-- Empty-stack emission is polynomial time for every fixed selected class and
stack. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (selected : Data → Bool) (stack : tm.K) :
    @TM2ComputableInPolyTime
      (List (AffineEmitterPipeline.Workspace Data))
      (List (AffineEmitterPipeline.Workspace Data))
      (AffineEmitterPipeline.Workspace Data)
      (AffineEmitterPipeline.Workspace Data) id id
      (run (tm := tm) selected stack) :=
  AffineEmitterPipeline.runAllComputableInPolyTime
    (phases (tm := tm) selected stack)

end BoundedMachineEmptyStackEmitter
end PeriodicCNF
end LeanTrominoes
