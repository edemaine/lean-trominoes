/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStackProgramEmitter

/-!
# Complete terminal statement-path emission

Surround a terminal path's runtime-width stack program by its fixed guard,
next-label and next-control operands and by the fixed four-input `all` ending.
The result is exactly `StatementProgramPath.program`.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStatementPathEmitter

open AffineEmitterPipeline
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def appendTokens {Data : Type} (tokens : List Token) :
    List (Workspace Data) → List (Workspace Data) :=
  (BoundedMachineOneHotEmitter.fixedPhase tokens).run

omit stackFinite in
theorem appendTokens_eq {Data : Type} (tokens : List Token)
    (workspace : List (Workspace Data)) :
    appendTokens tokens workspace =
      workspace ++ tokens.map fun token =>
        (Sum.inr token : Workspace Data) := by
  unfold appendTokens Phase.run BoundedMachineOneHotEmitter.fixedPhase
    AffineTemplateEmitterMachine.appendedOutput
  simp [BoundedMachineOneHotEmitter.positionRangeTokens_nil]

omit stackFinite in
@[simp]
theorem selectedCount_appendTokens {Data : Type} (selected : Data → Bool)
    (tokens : List Token) (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (appendTokens tokens workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [appendTokens_eq, AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

omit stackFinite in
noncomputable def appendTokensComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (tokens : List Token) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (appendTokens (Data := Data) tokens) :=
  (BoundedMachineOneHotEmitter.fixedPhase tokens).computableInPolyTime

def fixedPrefix (path : BoundedMachineProgram.StatementProgramPath tm) :
    List Token :=
  ofProgram path.guard ++
    ofProgram (BoundedMachineProgram.nextLabelIs (tm := tm) path.label) ++
    ofProgram (BoundedMachineProgram.nextControlIs (tm := tm) path.control)

def ending : List Token := allEnding 4

def emitted (path : BoundedMachineProgram.StatementProgramPath tm)
    (space : Nat) : List Token :=
  fixedPrefix (tm := tm) path ++
    BoundedMachineStackProgramEmitter.emitted (tm := tm) path space ++
    ending

def run {Data : Type} (selected : Data → Bool)
    (path : BoundedMachineProgram.StatementProgramPath tm)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  appendTokens ending
    (BoundedMachineStackProgramEmitter.run (tm := tm) selected path
      (appendTokens (fixedPrefix (tm := tm) path) workspace))

@[simp]
theorem selectedCount_stackRun {Data : Type} (selected : Data → Bool)
    (path : BoundedMachineProgram.StatementProgramPath tm)
    (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (BoundedMachineStackProgramEmitter.run (tm := tm)
          selected path workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [BoundedMachineStackProgramEmitter.run_eq_append,
    AffineEmitterPipeline.selectedCount_append,
    AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (path : BoundedMachineProgram.StatementProgramPath tm)
    (workspace : List (Workspace Data)) :
    run (tm := tm) selected path workspace =
      workspace ++
        (emitted (tm := tm) path
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [appendTokens_eq, BoundedMachineStackProgramEmitter.run_eq_append,
    selectedCount_appendTokens, appendTokens_eq]
  unfold emitted
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (path : BoundedMachineProgram.StatementProgramPath tm) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected path) := by
  let prefixCertificate := appendTokensComputableInPolyTime
    (Data := Data) (fixedPrefix (tm := tm) path)
  let stackCertificate :=
    BoundedMachineStackProgramEmitter.computableInPolyTime
      (tm := tm) selected path
  let throughStack := TM2CompositionMachine.computableInPolyTime
    prefixCertificate stackCertificate
  let complete := TM2CompositionMachine.computableInPolyTime throughStack
    (appendTokensComputableInPolyTime (Data := Data) ending)
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      appendTokens ending
        (BoundedMachineStackProgramEmitter.run (tm := tm) selected path
          (appendTokens (fixedPrefix (tm := tm) path) workspace)))
  exact complete

/-- The emitted word is exactly the terminal path's normalized program. -/
theorem emitted_eq_program
    (path : BoundedMachineProgram.StatementProgramPath tm) (space : Nat) :
    emitted (tm := tm) path space =
      ofProgram (path.program (tm := tm) (space := space)) := by
  unfold emitted fixedPrefix ending
    BoundedMachineProgram.StatementProgramPath.program
  rw [BoundedMachineStackProgramEmitter.emitted_eq_stackProgram,
    ofProgram_all]
  simp [List.append_assoc]

end BoundedMachineStatementPathEmitter
end PeriodicCNF
end LeanTrominoes
