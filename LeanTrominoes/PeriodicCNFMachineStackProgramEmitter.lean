/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStackTransformRangeEmitter
import LeanTrominoes.PeriodicCNFMachineProgramStatementPaths

/-!
# Complete stack-family program emission

Emit every normalized transform in the machine's canonical finite stack
order, then append the fixed `all` fold ending.  This is exactly the stack
program stored by a terminal symbolic statement path.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStackProgramEmitter

open AffineEmitterPipeline
open BoundedMachineAtom
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def stackList : List tm.K := finiteValues tm.K

def ending : List Token := allEnding (stackList (tm := tm)).length

def appendEnding {Data : Type} :
    List (Workspace Data) → List (Workspace Data) :=
  (BoundedMachineOneHotEmitter.fixedPhase (ending (tm := tm))).run

omit stackFinite in
theorem appendEnding_eq {Data : Type} (workspace : List (Workspace Data)) :
    appendEnding (tm := tm) workspace =
      workspace ++ (ending (tm := tm)).map fun token =>
        (Sum.inr token : Workspace Data) := by
  unfold appendEnding Phase.run BoundedMachineOneHotEmitter.fixedPhase
    AffineTemplateEmitterMachine.appendedOutput
  simp [BoundedMachineOneHotEmitter.positionRangeTokens_nil]

noncomputable def appendEndingComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (appendEnding (tm := tm) (Data := Data)) :=
  (BoundedMachineOneHotEmitter.fixedPhase
    (ending (tm := tm))).computableInPolyTime

def emitted (path : BoundedMachineProgram.StatementProgramPath tm)
    (space : Nat) : List Token :=
  BoundedMachineStackTransformRangeEmitter.emitted (tm := tm)
      path.transforms (stackList (tm := tm)) space ++
    ending (tm := tm)

def run {Data : Type} (selected : Data → Bool)
    (path : BoundedMachineProgram.StatementProgramPath tm)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  appendEnding (tm := tm)
    (BoundedMachineStackTransformRangeEmitter.run (tm := tm)
      selected path.transforms (stackList (tm := tm)) workspace)

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (path : BoundedMachineProgram.StatementProgramPath tm)
    (workspace : List (Workspace Data)) :
    run (tm := tm) selected path workspace =
      workspace ++
        (emitted (tm := tm) path
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [appendEnding_eq,
    BoundedMachineStackTransformRangeEmitter.run_eq_append]
  unfold emitted
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (path : BoundedMachineProgram.StatementProgramPath tm) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected path) := by
  let transformsCertificate :=
    BoundedMachineStackTransformRangeEmitter.computableInPolyTime
      (tm := tm) selected path.transforms (stackList (tm := tm))
  let complete := TM2CompositionMachine.computableInPolyTime
    transformsCertificate
      (appendEndingComputableInPolyTime (tm := tm) (Data := Data))
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      appendEnding (tm := tm)
        (BoundedMachineStackTransformRangeEmitter.run (tm := tm)
          selected path.transforms (stackList (tm := tm)) workspace))
  exact complete

/-- The emitted word is exactly the path's normalized stack-family program. -/
theorem emitted_eq_stackProgram
    (path : BoundedMachineProgram.StatementProgramPath tm) (space : Nat) :
    emitted (tm := tm) path space =
      ofProgram (path.stackProgram (tm := tm) (space := space)) := by
  unfold emitted BoundedMachineProgram.StatementProgramPath.stackProgram
    ending stackList
  rw [BoundedMachineStackTransformRangeEmitter.emitted_eq_programs,
    ofProgram_all]
  simp [List.flatMap_map]

end BoundedMachineStackProgramEmitter
end PeriodicCNF
end LeanTrominoes
