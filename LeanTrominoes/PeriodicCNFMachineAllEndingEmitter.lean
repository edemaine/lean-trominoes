/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineEmptyStackRangeEmitter

/-!
# Polynomial-time emission of an `all` fold ending

After Boolean operands have been emitted, a normalized right-associated
`TransitionProgram.all` contributes a constant-true base followed by one
conjunction closer per operand.  Two affine passes append that exact word while
preserving an arbitrary workspace.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNF
namespace BoundedMachineAllEndingEmitter

open AffineEmitterPipeline
open AffineProgramTemplates
open AffineTemplateEmitterMachine
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

def phases {Data : Type} (selected : Data → Bool) : List (Phase Data) :=
  [BoundedMachineOneHotEmitter.fixedPhase (allEnding 0),
    BoundedMachineEmptyStackEmitter.closerPhase selected]

def run {Data : Type} (selected : Data → Bool) :
    List (AffineEmitterPipeline.Workspace Data) →
      List (AffineEmitterPipeline.Workspace Data) :=
  runAll (phases selected)

theorem allEnding_eq_base_append_repeat (count : Nat) :
    allEnding count = allEnding 0 ++
      BoundedMachineOneHotEmitter.repeatInstructionTokens .conjoin count := by
  simpa [allEnding] using
    BoundedMachineOneHotEmitter.foldEnding_add true .conjoin 0 count

/-- The closer pass preserves the input and appends exactly `allEnding` at the
selected operand count. -/
theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (workspace : List (AffineEmitterPipeline.Workspace Data)) :
    run selected workspace =
      workspace ++
        (allEnding
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token =>
              (Sum.inr token : AffineEmitterPipeline.Workspace Data) := by
  let count := AffineTemplateEmitterMachine.selectedCount selected workspace
  have countAfterBase :
      AffineTemplateEmitterMachine.selectedCount selected
          (workspace ++ (allEnding 0).map fun token =>
            (Sum.inr token : AffineEmitterPipeline.Workspace Data)) = count := by
    rw [AffineEmitterPipeline.selectedCount_append,
      AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
  unfold run phases
  simp only [runAll]
  unfold Phase.run BoundedMachineOneHotEmitter.fixedPhase
    BoundedMachineEmptyStackEmitter.closerPhase
    AffineTemplateEmitterMachine.appendedOutput
  simp only [BoundedMachineOneHotEmitter.positionRangeTokens_nil,
    List.nil_append, List.append_nil]
  change (workspace ++ (allEnding 0).map fun token =>
      (Sum.inr token : AffineEmitterPipeline.Workspace Data)) ++
        (positionRangeTokens
          (AffineProgramTemplates.Program.recipes
            ([.conjoin] : AffineProgramTemplates.Program)) 0
          (AffineTemplateEmitterMachine.selectedCount selected
            (workspace ++ (allEnding 0).map fun token =>
              (Sum.inr token :
                AffineEmitterPipeline.Workspace Data)))).map Sum.inr = _
  rw [countAfterBase, BoundedMachineEmptyStackEmitter.closerRange_eq]
  unfold count
  rw [allEnding_eq_base_append_repeat
    (AffineTemplateEmitterMachine.selectedCount selected workspace)]
  simp [List.map_append, List.append_assoc]

/-- Emitting the fold ending is polynomial time for every fixed selector. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (selected : Data → Bool) :
    @TM2ComputableInPolyTime
      (List (AffineEmitterPipeline.Workspace Data))
      (List (AffineEmitterPipeline.Workspace Data))
      (AffineEmitterPipeline.Workspace Data)
      (AffineEmitterPipeline.Workspace Data) id id
      (run selected) :=
  AffineEmitterPipeline.runAllComputableInPolyTime (phases selected)

end BoundedMachineAllEndingEmitter
end PeriodicCNF
end LeanTrominoes
