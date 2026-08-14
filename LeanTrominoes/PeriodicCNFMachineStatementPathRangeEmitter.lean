/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStatementPathEmitter

/-!
# Emission of a fixed terminal-path disjunction

Iterate the complete terminal-path emitter over a fixed path list and append
the corresponding fixed `any` ending.  This isolates runtime-dependent path
selection from emission of the selected finite list.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStatementPathRangeEmitter

open AffineEmitterPipeline
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data
abbrev Path := BoundedMachineProgram.StatementProgramPath tm

def operandTokens (paths : List (Path (tm := tm))) (space : Nat) : List Token :=
  paths.flatMap fun path =>
    BoundedMachineStatementPathEmitter.emitted (tm := tm) path space

def emitted (paths : List (Path (tm := tm))) (space : Nat) : List Token :=
  operandTokens (tm := tm) paths space ++ anyEnding paths.length

def runOperands {Data : Type} (selected : Data → Bool) :
    List (Path (tm := tm)) → List (Workspace Data) → List (Workspace Data)
  | [], workspace => workspace
  | path :: paths, workspace =>
      runOperands selected paths
        (BoundedMachineStatementPathEmitter.run (tm := tm)
          selected path workspace)

@[simp]
theorem selectedCount_runOperands {Data : Type} (selected : Data → Bool)
    (paths : List (Path (tm := tm))) (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (runOperands (tm := tm) selected paths workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  induction paths generalizing workspace with
  | nil => rfl
  | cons path paths induction =>
      rw [runOperands, induction]
      rw [BoundedMachineStatementPathEmitter.run_eq_append,
        AffineEmitterPipeline.selectedCount_append,
        AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

theorem runOperands_eq_append {Data : Type} (selected : Data → Bool)
    (paths : List (Path (tm := tm))) (workspace : List (Workspace Data)) :
    runOperands (tm := tm) selected paths workspace =
      workspace ++
        (operandTokens (tm := tm) paths
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  induction paths generalizing workspace with
  | nil => simp [runOperands, operandTokens]
  | cons path paths induction =>
      let space :=
        AffineTemplateEmitterMachine.selectedCount selected workspace
      let first := BoundedMachineStatementPathEmitter.run (tm := tm)
        selected path workspace
      have firstEq : first = workspace ++
          (BoundedMachineStatementPathEmitter.emitted (tm := tm)
            path space).map fun token =>
              (Sum.inr token : Workspace Data) := by
        exact BoundedMachineStatementPathEmitter.run_eq_append
          (tm := tm) selected path workspace
      have spaceEq :
          AffineTemplateEmitterMachine.selectedCount selected first =
            space := by
        unfold first
        rw [BoundedMachineStatementPathEmitter.run_eq_append,
          AffineEmitterPipeline.selectedCount_append,
          AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
      rw [runOperands]
      change runOperands (tm := tm) selected paths first = _
      rw [induction, spaceEq, firstEq]
      unfold operandTokens space
      simp [List.map_append, List.append_assoc]

noncomputable def runOperandsComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool) :
    (paths : List (Path (tm := tm))) →
      @TM2ComputableInPolyTime
        (List (Workspace Data)) (List (Workspace Data))
        (Workspace Data) (Workspace Data) id id
        (runOperands (tm := tm) selected paths)
  | [] => AffineEmitterPipeline.identityComputableInPolyTime
  | path :: paths => by
      let complete := TM2CompositionMachine.computableInPolyTime
        (BoundedMachineStatementPathEmitter.computableInPolyTime
          (tm := tm) selected path)
        (runOperandsComputableInPolyTime selected paths)
      simpa only [runOperands] using complete

def run {Data : Type} (selected : Data → Bool)
    (paths : List (Path (tm := tm)))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  BoundedMachineStatementPathEmitter.appendTokens (anyEnding paths.length)
    (runOperands (tm := tm) selected paths workspace)

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (paths : List (Path (tm := tm))) (workspace : List (Workspace Data)) :
    run (tm := tm) selected paths workspace =
      workspace ++
        (emitted (tm := tm) paths
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [BoundedMachineStatementPathEmitter.appendTokens_eq,
    runOperands_eq_append]
  unfold emitted
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (paths : List (Path (tm := tm))) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected paths) := by
  let operandsCertificate := runOperandsComputableInPolyTime
    (tm := tm) selected paths
  let complete := TM2CompositionMachine.computableInPolyTime
    operandsCertificate
    (BoundedMachineStatementPathEmitter.appendTokensComputableInPolyTime
      (Data := Data) (anyEnding paths.length))
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      BoundedMachineStatementPathEmitter.appendTokens
        (anyEnding paths.length)
        (runOperands (tm := tm) selected paths workspace))
  exact complete

/-- Exact normalized disjunction of the supplied terminal path list. -/
theorem emitted_eq_anyPrograms (paths : List (Path (tm := tm)))
    (space : Nat) :
    emitted (tm := tm) paths space =
      ofProgram
        (TransitionProgram.any (paths.map fun path =>
          path.program (tm := tm) (space := space))) := by
  unfold emitted operandTokens
  rw [ofProgram_any]
  simp only [List.length_map]
  rw [List.flatMap_map]
  apply congrArg₂ (· ++ ·)
  · apply List.flatMap_congr
    intro path _
    exact BoundedMachineStatementPathEmitter.emitted_eq_program
      (tm := tm) path space
  · rfl

end BoundedMachineStatementPathRangeEmitter
end PeriodicCNF
end LeanTrominoes
