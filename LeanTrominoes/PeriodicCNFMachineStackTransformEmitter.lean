/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStackTransformFitsEmitter
import LeanTrominoes.PeriodicCNFMachineStackTransformCellSchedule
import LeanTrominoes.PeriodicCNFMachineAllEndingEmitter

/-!
# Complete bounded stack-transform emission

Compose the fit operand, every represented cell operand, the normalized
`all` fold ending, and the final conjunction.  The resulting token stream is
exactly one complete normalized stack-transform program.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStackTransformEmitter

open AffineEmitterPipeline
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def finalTokens : List Token :=
  instructionTokens .conjoin

def appendFinal {Data : Type} :
    List (Workspace Data) → List (Workspace Data) :=
  (BoundedMachineOneHotEmitter.fixedPhase finalTokens).run

theorem appendFinal_eq {Data : Type} (workspace : List (Workspace Data)) :
    appendFinal workspace =
      workspace ++ finalTokens.map fun token =>
        (Sum.inr token : Workspace Data) := by
  unfold appendFinal Phase.run BoundedMachineOneHotEmitter.fixedPhase
    AffineTemplateEmitterMachine.appendedOutput
  simp [BoundedMachineOneHotEmitter.positionRangeTokens_nil]

noncomputable def appendFinalComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (appendFinal (Data := Data)) :=
  (BoundedMachineOneHotEmitter.fixedPhase finalTokens).computableInPolyTime

def emitted (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (space : Nat) : List Token :=
  BoundedMachineStackTransformFitsEmitter.emitted (tm := tm) stack
      transform space ++
    BoundedMachineStackTransformCellEmitter.emitted (tm := tm) stack
      transform space ++
    allEnding space ++ finalTokens

def run {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  appendFinal
    (BoundedMachineAllEndingEmitter.run selected
      (BoundedMachineStackTransformCellEmitter.run (tm := tm)
        selected stack transform
        (BoundedMachineStackTransformFitsEmitter.run (tm := tm)
          selected stack transform workspace)))

@[simp]
theorem selectedCount_fitsRun {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (BoundedMachineStackTransformFitsEmitter.run (tm := tm)
          selected stack transform workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [BoundedMachineStackTransformFitsEmitter.run_eq_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

@[simp]
theorem selectedCount_cellRun {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (BoundedMachineStackTransformCellEmitter.run (tm := tm)
          selected stack transform workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [BoundedMachineStackTransformCellEmitter.run_eq_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    run (tm := tm) selected stack transform workspace =
      workspace ++
        (emitted (tm := tm) stack transform
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [appendFinal_eq, BoundedMachineAllEndingEmitter.run_eq_append,
    selectedCount_cellRun, selectedCount_fitsRun,
    BoundedMachineStackTransformCellEmitter.run_eq_append,
    selectedCount_fitsRun,
    BoundedMachineStackTransformFitsEmitter.run_eq_append]
  unfold emitted
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected stack transform) := by
  let fitsCertificate :=
    BoundedMachineStackTransformFitsEmitter.computableInPolyTime
      (tm := tm) selected stack transform
  let cellCertificate :=
    BoundedMachineStackTransformCellEmitter.computableInPolyTime
      (tm := tm) selected stack transform
  let throughCells := TM2CompositionMachine.computableInPolyTime
    fitsCertificate cellCertificate
  let throughAllEnding := TM2CompositionMachine.computableInPolyTime
    throughCells
      (BoundedMachineAllEndingEmitter.computableInPolyTime selected)
  let complete := TM2CompositionMachine.computableInPolyTime
    throughAllEnding (appendFinalComputableInPolyTime (Data := Data))
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      appendFinal
        (BoundedMachineAllEndingEmitter.run selected
          (BoundedMachineStackTransformCellEmitter.run (tm := tm)
            selected stack transform
            (BoundedMachineStackTransformFitsEmitter.run (tm := tm)
              selected stack transform workspace))))
  exact complete

/-- Exact token identity for the complete normalized stack transform. -/
theorem emitted_eq_stackTransform (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    emitted (tm := tm) stack transform space =
      ofProgram
        (BoundedMachineProgram.stackTransform (tm := tm) (space := space)
          stack transform) := by
  unfold emitted BoundedMachineProgram.stackTransform finalTokens
  rw [BoundedMachineStackTransformFitsEmitter.emitted_eq_stackTransformFits,
    BoundedMachineStackTransformCellSchedule.emitted_eq_normalizedCellTokens]
  unfold BoundedMachineStackTransformCellSchedule.normalizedCellTokens
  rw [ofProgram_conjoin, ofProgram_all]
  simp [List.append_assoc, List.flatMap_map]

end BoundedMachineStackTransformEmitter
end PeriodicCNF
end LeanTrominoes
