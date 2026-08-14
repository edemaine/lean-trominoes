/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStatementPathsEmitter

/-!
# Complete bounded statement-program emission

For each fixed finite-control value, emit its current-control test followed by
the runtime symbolic-path disjunction and a conjunction closer.  Iterate the
fixed control list and append its `any` ending to obtain the exact normalized
`statementProgram`.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStatementEmitter

open AffineEmitterPipeline
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def controlPrefix (control : tm.σ) : List Token :=
  ofProgram (BoundedMachineProgram.currentControlIs (tm := tm) control)

def controlEnding : List Token := instructionTokens .conjoin

def controlTokens
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (space : Nat) : List Token :=
  controlPrefix (tm := tm) control ++
    BoundedMachineStatementPathsEmitter.emitted (tm := tm)
      statement control space ++ controlEnding

def runControl {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (workspace : List (Workspace Data)) :
    List (Workspace Data) :=
  BoundedMachineStatementPathEmitter.appendTokens controlEnding
    (BoundedMachineStatementPathsEmitter.run (tm := tm)
      selected statement control
      (BoundedMachineStatementPathEmitter.appendTokens
        (controlPrefix (tm := tm) control) workspace))

@[simp]
theorem selectedCount_pathsRun {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (BoundedMachineStatementPathsEmitter.run (tm := tm)
          selected statement control workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [BoundedMachineStatementPathsEmitter.run_eq_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

theorem runControl_eq_append {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (workspace : List (Workspace Data)) :
    runControl (tm := tm) selected statement control workspace =
      workspace ++
        (controlTokens (tm := tm) statement control
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold runControl
  rw [BoundedMachineStatementPathEmitter.appendTokens_eq,
    BoundedMachineStatementPathsEmitter.run_eq_append,
    BoundedMachineStatementPathEmitter.selectedCount_appendTokens,
    BoundedMachineStatementPathEmitter.appendTokens_eq]
  unfold controlTokens
  simp [List.map_append, List.append_assoc]

@[simp]
theorem selectedCount_runControl {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (runControl (tm := tm) selected statement control workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [runControl_eq_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

noncomputable def runControlComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (runControl (tm := tm) selected statement control) := by
  let prefixCertificate :=
    BoundedMachineStatementPathEmitter.appendTokensComputableInPolyTime
      (Data := Data) (controlPrefix (tm := tm) control)
  let pathsCertificate :=
    BoundedMachineStatementPathsEmitter.computableInPolyTime
      (tm := tm) selected statement control
  let throughPaths := TM2CompositionMachine.computableInPolyTime
    prefixCertificate pathsCertificate
  let complete := TM2CompositionMachine.computableInPolyTime throughPaths
    (BoundedMachineStatementPathEmitter.appendTokensComputableInPolyTime
      (Data := Data) controlEnding)
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      BoundedMachineStatementPathEmitter.appendTokens controlEnding
        (BoundedMachineStatementPathsEmitter.run (tm := tm)
          selected statement control
          (BoundedMachineStatementPathEmitter.appendTokens
            (controlPrefix (tm := tm) control) workspace)))
  exact complete

def operandTokens
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (controls : List tm.σ) (space : Nat) : List Token :=
  controls.flatMap fun control =>
    controlTokens (tm := tm) statement control space

def runControls {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    List tm.σ → List (Workspace Data) → List (Workspace Data)
  | [], workspace => workspace
  | control :: controls, workspace =>
      runControls selected statement controls
        (runControl (tm := tm) selected statement control workspace)

theorem runControls_eq_append {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (controls : List tm.σ) (workspace : List (Workspace Data)) :
    runControls (tm := tm) selected statement controls workspace =
      workspace ++
        (operandTokens (tm := tm) statement controls
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  induction controls generalizing workspace with
  | nil => simp [runControls, operandTokens]
  | cons control controls induction =>
      let space :=
        AffineTemplateEmitterMachine.selectedCount selected workspace
      let first := runControl (tm := tm) selected statement control workspace
      have firstEq : first = workspace ++
          (controlTokens (tm := tm) statement control space).map fun token =>
            (Sum.inr token : Workspace Data) := by
        exact runControl_eq_append (tm := tm)
          selected statement control workspace
      have spaceEq :
          AffineTemplateEmitterMachine.selectedCount selected first =
            space := by
        unfold first
        rw [selectedCount_runControl]
      rw [runControls]
      change runControls (tm := tm) selected statement controls first = _
      rw [induction, spaceEq, firstEq]
      unfold operandTokens space
      simp [List.map_append, List.append_assoc]

noncomputable def runControlsComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (controls : List tm.σ) →
      @TM2ComputableInPolyTime
        (List (Workspace Data)) (List (Workspace Data))
        (Workspace Data) (Workspace Data) id id
        (runControls (tm := tm) selected statement controls)
  | [] => AffineEmitterPipeline.identityComputableInPolyTime
  | control :: controls => by
      let complete := TM2CompositionMachine.computableInPolyTime
        (runControlComputableInPolyTime (tm := tm)
          selected statement control)
        (runControlsComputableInPolyTime selected statement controls)
      simpa only [runControls] using complete

def controls : List tm.σ := BoundedMachineAtom.finiteValues tm.σ

def ending : List Token := anyEnding (controls (tm := tm)).length

def emitted
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (space : Nat) : List Token :=
  operandTokens (tm := tm) statement (controls (tm := tm)) space ++
    ending (tm := tm)

def run {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  BoundedMachineStatementPathEmitter.appendTokens (ending (tm := tm))
    (runControls (tm := tm) selected statement (controls (tm := tm)) workspace)

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (workspace : List (Workspace Data)) :
    run (tm := tm) selected statement workspace =
      workspace ++
        (emitted (tm := tm) statement
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [BoundedMachineStatementPathEmitter.appendTokens_eq,
    runControls_eq_append]
  unfold emitted
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected statement) := by
  let controlsCertificate := runControlsComputableInPolyTime
    (tm := tm) selected statement (controls (tm := tm))
  let complete := TM2CompositionMachine.computableInPolyTime
    controlsCertificate
    (BoundedMachineStatementPathEmitter.appendTokensComputableInPolyTime
      (Data := Data) (ending (tm := tm)))
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      BoundedMachineStatementPathEmitter.appendTokens (ending (tm := tm))
        (runControls (tm := tm) selected statement
          (controls (tm := tm)) workspace))
  exact complete

theorem controlTokens_eq_program
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (space : Nat) :
    controlTokens (tm := tm) statement control space =
      ofProgram
        (TransitionProgram.conjoin
          (BoundedMachineProgram.currentControlIs (tm := tm) control)
          (BoundedMachineProgram.statementPathsProgram (tm := tm)
            (space := space) statement control
            BoundedMachineAtom.identityStackTransforms)) := by
  unfold controlTokens controlPrefix controlEnding
  rw [BoundedMachineStatementPathsEmitter.emitted_eq_statementPathsProgram,
    ofProgram_conjoin]

/-- Exact normalized program for one fixed machine statement. -/
theorem emitted_eq_statementProgram
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (space : Nat) :
    emitted (tm := tm) statement space =
      ofProgram
        (BoundedMachineProgram.statementProgram (tm := tm)
          (space := space) statement) := by
  unfold emitted operandTokens controls ending
    BoundedMachineProgram.statementProgram
  rw [ofProgram_any]
  simp only [List.length_map]
  rw [List.flatMap_map]
  apply congrArg₂ (· ++ ·)
  · apply List.flatMap_congr
    intro control _
    exact controlTokens_eq_program (tm := tm) statement control space
  · rfl

end BoundedMachineStatementEmitter
end PeriodicCNF
end LeanTrominoes
