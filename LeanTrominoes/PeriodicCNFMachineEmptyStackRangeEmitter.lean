/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialStackOrder

/-!
# Polynomial-time emission of a fixed list of empty stacks

Iterate the verified one-stack pass over a fixed stack list.  Every pass only
appends tokens, so the selected runtime width remains invariant; the complete
word is consequently the stack-order flat map of the exact per-stack words.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineEmptyStackRangeEmitter

open AffineEmitterPipeline
open AffineTemplateEmitterMachine
open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def emitted (stackList : List tm.K) (count : Nat) : List Token :=
  stackList.flatMap fun stack =>
    BoundedMachineEmptyStackEmitter.emitted (tm := tm) stack count

def run {Data : Type} (selected : Data → Bool) :
    List tm.K → List (AffineEmitterPipeline.Workspace Data) →
      List (AffineEmitterPipeline.Workspace Data)
  | [], workspace => workspace
  | stack :: stackList, workspace =>
      run selected stackList
        (BoundedMachineEmptyStackEmitter.run (tm := tm)
          selected stack workspace)

@[simp]
theorem selectedCount_run {Data : Type} (selected : Data → Bool)
    (stackList : List tm.K)
    (workspace : List (AffineEmitterPipeline.Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (run (tm := tm) selected stackList workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  induction stackList generalizing workspace with
  | nil => rfl
  | cons stack stackList induction =>
      rw [run, induction]
      rw [BoundedMachineEmptyStackEmitter.run_eq_append,
        AffineEmitterPipeline.selectedCount_append,
        AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]

/-- The complete fixed stack list preserves the workspace and appends exactly
the ordered concatenation of its empty-stack schedules. -/
theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (stackList : List tm.K)
    (workspace : List (AffineEmitterPipeline.Workspace Data)) :
    run (tm := tm) selected stackList workspace =
      workspace ++
        (emitted (tm := tm) stackList
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token =>
              (Sum.inr token : AffineEmitterPipeline.Workspace Data) := by
  induction stackList generalizing workspace with
  | nil => simp [run, emitted]
  | cons stack stackList induction =>
      let count := AffineTemplateEmitterMachine.selectedCount selected workspace
      let first := BoundedMachineEmptyStackEmitter.run (tm := tm)
        selected stack workspace
      have firstEq : first = workspace ++
          (BoundedMachineEmptyStackEmitter.emitted (tm := tm) stack count).map
            (fun token =>
              (Sum.inr token : AffineEmitterPipeline.Workspace Data)) := by
        exact BoundedMachineEmptyStackEmitter.run_eq_append
          (tm := tm) selected stack workspace
      have countEq : AffineTemplateEmitterMachine.selectedCount selected first =
          count := by
        unfold first
        rw [BoundedMachineEmptyStackEmitter.run_eq_append,
          AffineEmitterPipeline.selectedCount_append,
          AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
      rw [run]
      change run (tm := tm) selected stackList first = _
      rw [induction, countEq, firstEq]
      unfold emitted count
      simp [List.map_append, List.append_assoc]

/-- Iterating any fixed finite stack list is polynomial time. -/
noncomputable def computableInPolyTime {Data : Type} [Fintype Data]
    [Inhabited Data] (selected : Data → Bool) :
    (stackList : List tm.K) →
      @TM2ComputableInPolyTime
        (List (AffineEmitterPipeline.Workspace Data))
        (List (AffineEmitterPipeline.Workspace Data))
        (AffineEmitterPipeline.Workspace Data)
        (AffineEmitterPipeline.Workspace Data) id id
        (run (tm := tm) selected stackList)
  | [] => AffineEmitterPipeline.identityComputableInPolyTime
  | stack :: stackList => by
      let complete := TM2CompositionMachine.computableInPolyTime
        (BoundedMachineEmptyStackEmitter.computableInPolyTime
          (tm := tm) selected stack)
        (computableInPolyTime selected stackList)
      simpa only [run] using complete

end BoundedMachineEmptyStackRangeEmitter
end PeriodicCNF
end LeanTrominoes
