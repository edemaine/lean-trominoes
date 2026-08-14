/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStatementEmitter

/-!
# Complete ordinary bounded-machine step emission

For every fixed live program label, emit its current-label guard followed by
the exact statement program and a conjunction closer.  Iterating the fixed
label list and appending its `any` ending yields the exact normalized
`machineStep` program.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStepEmitter

open AffineEmitterPipeline
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def labelPrefix (label : tm.Λ) : List Token :=
  ofProgram
    (BoundedMachineProgram.currentLabelIs (tm := tm) (some label))

def labelEnding : List Token := instructionTokens .conjoin

def labelTokens (label : tm.Λ) (space : Nat) : List Token :=
  labelPrefix (tm := tm) label ++
    BoundedMachineStatementEmitter.emitted (tm := tm) (tm.m label) space ++
    labelEnding

def runLabel {Data : Type} (selected : Data → Bool) (label : tm.Λ)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  BoundedMachineStatementPathEmitter.appendTokens labelEnding
    (BoundedMachineStatementEmitter.run (tm := tm)
      selected (tm.m label)
      (BoundedMachineStatementPathEmitter.appendTokens
        (labelPrefix (tm := tm) label) workspace))

theorem runLabel_eq_append {Data : Type} (selected : Data → Bool)
    (label : tm.Λ) (workspace : List (Workspace Data)) :
    runLabel (tm := tm) selected label workspace =
      workspace ++
        (labelTokens (tm := tm) label
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold runLabel
  rw [BoundedMachineStatementPathEmitter.appendTokens_eq,
    BoundedMachineStatementEmitter.run_eq_append,
    BoundedMachineStatementPathEmitter.selectedCount_appendTokens,
    BoundedMachineStatementPathEmitter.appendTokens_eq]
  unfold labelTokens
  simp [List.map_append, List.append_assoc]

@[simp]
theorem selectedCount_runLabel {Data : Type} (selected : Data → Bool)
    (label : tm.Λ) (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (runLabel (tm := tm) selected label workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [runLabel_eq_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

noncomputable def runLabelComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (label : tm.Λ) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (runLabel (tm := tm) selected label) := by
  let prefixCertificate :=
    BoundedMachineStatementPathEmitter.appendTokensComputableInPolyTime
      (Data := Data) (labelPrefix (tm := tm) label)
  let statementCertificate :=
    BoundedMachineStatementEmitter.computableInPolyTime
      (tm := tm) selected (tm.m label)
  let throughStatement := TM2CompositionMachine.computableInPolyTime
    prefixCertificate statementCertificate
  let complete := TM2CompositionMachine.computableInPolyTime
    throughStatement
    (BoundedMachineStatementPathEmitter.appendTokensComputableInPolyTime
      (Data := Data) labelEnding)
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      BoundedMachineStatementPathEmitter.appendTokens labelEnding
        (BoundedMachineStatementEmitter.run (tm := tm)
          selected (tm.m label)
          (BoundedMachineStatementPathEmitter.appendTokens
            (labelPrefix (tm := tm) label) workspace)))
  exact complete

def operandTokens (labels : List tm.Λ) (space : Nat) : List Token :=
  labels.flatMap fun label => labelTokens (tm := tm) label space

def runLabels {Data : Type} (selected : Data → Bool) :
    List tm.Λ → List (Workspace Data) → List (Workspace Data)
  | [], workspace => workspace
  | label :: labels, workspace =>
      runLabels selected labels
        (runLabel (tm := tm) selected label workspace)

theorem runLabels_eq_append {Data : Type} (selected : Data → Bool)
    (labels : List tm.Λ) (workspace : List (Workspace Data)) :
    runLabels (tm := tm) selected labels workspace =
      workspace ++
        (operandTokens (tm := tm) labels
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  induction labels generalizing workspace with
  | nil => simp [runLabels, operandTokens]
  | cons label labels induction =>
      let space :=
        AffineTemplateEmitterMachine.selectedCount selected workspace
      let first := runLabel (tm := tm) selected label workspace
      have firstEq : first = workspace ++
          (labelTokens (tm := tm) label space).map fun token =>
            (Sum.inr token : Workspace Data) := by
        exact runLabel_eq_append (tm := tm) selected label workspace
      have spaceEq :
          AffineTemplateEmitterMachine.selectedCount selected first =
            space := by
        unfold first
        rw [selectedCount_runLabel]
      rw [runLabels]
      change runLabels (tm := tm) selected labels first = _
      rw [induction, spaceEq, firstEq]
      unfold operandTokens space
      simp [List.map_append, List.append_assoc]

noncomputable def runLabelsComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool) :
    (labels : List tm.Λ) →
      @TM2ComputableInPolyTime
        (List (Workspace Data)) (List (Workspace Data))
        (Workspace Data) (Workspace Data) id id
        (runLabels (tm := tm) selected labels)
  | [] => AffineEmitterPipeline.identityComputableInPolyTime
  | label :: labels => by
      let complete := TM2CompositionMachine.computableInPolyTime
        (runLabelComputableInPolyTime (tm := tm) selected label)
        (runLabelsComputableInPolyTime selected labels)
      simpa only [runLabels] using complete

def labels : List tm.Λ := BoundedMachineAtom.finiteValues tm.Λ

def ending : List Token := anyEnding (labels (tm := tm)).length

def emitted (space : Nat) : List Token :=
  operandTokens (tm := tm) (labels (tm := tm)) space ++ ending (tm := tm)

def run {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  BoundedMachineStatementPathEmitter.appendTokens (ending (tm := tm))
    (runLabels (tm := tm) selected (labels (tm := tm)) workspace)

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) :
    run (tm := tm) selected workspace =
      workspace ++
        (emitted (tm := tm)
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [BoundedMachineStatementPathEmitter.appendTokens_eq,
    runLabels_eq_append]
  unfold emitted
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected) := by
  let labelsCertificate := runLabelsComputableInPolyTime
    (tm := tm) selected (labels (tm := tm))
  let complete := TM2CompositionMachine.computableInPolyTime
    labelsCertificate
    (BoundedMachineStatementPathEmitter.appendTokensComputableInPolyTime
      (Data := Data) (ending (tm := tm)))
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      BoundedMachineStatementPathEmitter.appendTokens (ending (tm := tm))
        (runLabels (tm := tm) selected (labels (tm := tm)) workspace))
  exact complete

theorem labelTokens_eq_program (label : tm.Λ) (space : Nat) :
    labelTokens (tm := tm) label space =
      ofProgram
        (TransitionProgram.conjoin
          (BoundedMachineProgram.currentLabelIs (tm := tm) (some label))
          (BoundedMachineProgram.statementProgram (tm := tm)
            (space := space) (tm.m label))) := by
  unfold labelTokens labelPrefix labelEnding
  rw [BoundedMachineStatementEmitter.emitted_eq_statementProgram,
    ofProgram_conjoin]

/-- Exact complete normalized ordinary machine-step program. -/
theorem emitted_eq_machineStep (space : Nat) :
    emitted (tm := tm) space =
      ofProgram
        (BoundedMachineProgram.machineStep (tm := tm) (space := space)) := by
  unfold emitted operandTokens labels ending BoundedMachineProgram.machineStep
  rw [ofProgram_any]
  simp only [List.length_map]
  rw [List.flatMap_map]
  apply congrArg₂ (· ++ ·)
  · apply List.flatMap_congr
    intro label _
    exact labelTokens_eq_program (tm := tm) label space
  · rfl

end BoundedMachineStepEmitter
end PeriodicCNF
end LeanTrominoes
