/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStackTransformEmitter

/-!
# Emission over a fixed list of bounded stack transforms

Iterate the complete one-transform emitter over a fixed stack list.  Every
pass preserves the selected runtime width, so the result is the ordered
flat-map of the exact normalized transform programs.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStackTransformRangeEmitter

open AffineEmitterPipeline
open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def emitted (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (stackList : List tm.K) (space : Nat) : List Token :=
  stackList.flatMap fun stack =>
    BoundedMachineStackTransformEmitter.emitted (tm := tm) stack
      (transforms stack) space

def run {Data : Type} (selected : Data → Bool)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    List tm.K → List (Workspace Data) → List (Workspace Data)
  | [], workspace => workspace
  | stack :: stackList, workspace =>
      run selected transforms stackList
        (BoundedMachineStackTransformEmitter.run (tm := tm)
          selected stack (transforms stack) workspace)

@[simp]
theorem selectedCount_run {Data : Type} (selected : Data → Bool)
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (stackList : List tm.K) (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (run (tm := tm) selected transforms stackList workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  induction stackList generalizing workspace with
  | nil => rfl
  | cons stack stackList induction =>
      rw [run, induction]
      rw [BoundedMachineStackTransformEmitter.run_eq_append,
        AffineEmitterPipeline.selectedCount_append,
        AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (stackList : List tm.K) (workspace : List (Workspace Data)) :
    run (tm := tm) selected transforms stackList workspace =
      workspace ++
        (emitted (tm := tm) transforms stackList
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  induction stackList generalizing workspace with
  | nil => simp [run, emitted]
  | cons stack stackList induction =>
      let space :=
        AffineTemplateEmitterMachine.selectedCount selected workspace
      let first := BoundedMachineStackTransformEmitter.run (tm := tm)
        selected stack (transforms stack) workspace
      have firstEq : first = workspace ++
          (BoundedMachineStackTransformEmitter.emitted (tm := tm) stack
            (transforms stack) space).map fun token =>
              (Sum.inr token : Workspace Data) := by
        exact BoundedMachineStackTransformEmitter.run_eq_append
          (tm := tm) selected stack (transforms stack) workspace
      have spaceEq :
          AffineTemplateEmitterMachine.selectedCount selected first =
            space := by
        unfold first
        rw [BoundedMachineStackTransformEmitter.run_eq_append,
          AffineEmitterPipeline.selectedCount_append,
          AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
      rw [run]
      change run (tm := tm) selected transforms stackList first = _
      rw [induction, spaceEq, firstEq]
      unfold emitted space
      simp [List.map_append, List.append_assoc]

/-- Iterating a fixed finite stack list remains polynomial time. -/
noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (stackList : List tm.K) →
      @TM2ComputableInPolyTime
        (List (Workspace Data)) (List (Workspace Data))
        (Workspace Data) (Workspace Data) id id
        (run (tm := tm) selected transforms stackList)
  | [] => AffineEmitterPipeline.identityComputableInPolyTime
  | stack :: stackList => by
      let complete := TM2CompositionMachine.computableInPolyTime
        (BoundedMachineStackTransformEmitter.computableInPolyTime
          (tm := tm) selected stack (transforms stack))
        (computableInPolyTime selected transforms stackList)
      simpa only [run] using complete

/-- The emitted range is exactly the concatenation of the normalized stack
transform programs in the requested stack order. -/
theorem emitted_eq_programs
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (stackList : List tm.K) (space : Nat) :
    emitted (tm := tm) transforms stackList space =
      stackList.flatMap fun stack =>
        ofProgram
          (BoundedMachineProgram.stackTransform (tm := tm) (space := space)
            stack (transforms stack)) := by
  unfold emitted
  apply List.flatMap_congr
  intro stack _
  exact BoundedMachineStackTransformEmitter.emitted_eq_stackTransform
    (tm := tm) stack (transforms stack) space

end BoundedMachineStackTransformRangeEmitter
end PeriodicCNF
end LeanTrominoes
