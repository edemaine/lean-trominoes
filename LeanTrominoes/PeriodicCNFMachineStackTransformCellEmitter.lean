/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStackTransformPrefixEmitter

/-!
# Complete bounded stack-transform cell emission

Complete the pushed-prefix and shifted-equality schedule with the final cells
whose transformed source position lies outside the represented width.  Their
absolute positions are `added.length + (space - cutoff) + offset`, where the
marked interval `[added.length, cutoff)` supplies exactly the required number
of offsets.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStackTransformCellEmitter

open AffineEmitterPipeline
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def workspaceSelected {Data : Type} (selected : Data → Bool) :
    Workspace Data → Bool :=
  BoundedMachineStackTransformPrefixEmitter.workspaceSelected selected

def cutoff {stack : tm.K} (transform : StackTransform (tm.Γ stack)) : Nat :=
  BoundedMachineStackTransformPrefixEmitter.cutoff transform

def tailProgram (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    BivariateProgramTemplates.Program :=
  BoundedMachineBivariateStack.nextStackCellIs (tm := tm) stack
    transform.added.length none

def tailTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : List Token :=
  BivariateTemplateEmitterMachine.positionRangeTokens
    (tailProgram (tm := tm) stack transform).recipes
    (space - cutoff transform) 0
    ((space - transform.added.length) - (space - cutoff transform))

def runTail {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  MarkedBivariateEmitterPipeline.run (workspaceSelected selected)
    (cutoff transform)
    (afterPrefix (workspaceSelected selected) (cutoff transform))
    (betweenPrefixes (workspaceSelected selected)
      transform.added.length (cutoff transform))
    (tailProgram (tm := tm) stack transform).recipes [] workspace

theorem runTail_eq_append {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    runTail (tm := tm) selected stack transform workspace =
      workspace ++
        (tailTokens (tm := tm) stack transform
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold runTail
  rw [MarkedBivariateEmitterPipeline.run_eq_append]
  unfold MarkedBivariateEmitterPipeline.emitted tailTokens
  have addedLe : transform.added.length ≤ cutoff transform := by
    unfold cutoff BoundedMachineStackTransformPrefixEmitter.cutoff
    omega
  rw [selectedCount_afterPrefix_mark
      (workspaceSelected selected) (Nat.le_refl (cutoff transform)),
    selectedCount_betweenPrefixes_mark
      (workspaceSelected selected) addedLe
      (Nat.le_refl (cutoff transform))]
  have selectedEq : UnaryPolynomialPaddingMachine.selectedCount
      (workspaceSelected selected) workspace =
      AffineTemplateEmitterMachine.selectedCount selected workspace := rfl
  rw [selectedEq]
  simp

noncomputable def runTailComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (runTail (tm := tm) selected stack transform) :=
  MarkedBivariateEmitterPipeline.computableInPolyTime
    (workspaceSelected selected) (cutoff transform)
    (afterPrefix (workspaceSelected selected) (cutoff transform))
    (betweenPrefixes (workspaceSelected selected)
      transform.added.length (cutoff transform))
    (tailProgram (tm := tm) stack transform).recipes []

def emitted (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (space : Nat) : List Token :=
  BoundedMachineStackTransformPrefixEmitter.emitted (tm := tm) stack
      transform space ++
    tailTokens (tm := tm) stack transform space

def run {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  runTail (tm := tm) selected stack transform
    (BoundedMachineStackTransformPrefixEmitter.run (tm := tm)
      selected stack transform workspace)

@[simp]
theorem selectedCount_prefix_run {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (BoundedMachineStackTransformPrefixEmitter.run (tm := tm)
          selected stack transform workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [BoundedMachineStackTransformPrefixEmitter.run_eq_append,
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
  rw [runTail_eq_append, selectedCount_prefix_run,
    BoundedMachineStackTransformPrefixEmitter.run_eq_append]
  unfold emitted
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected stack transform) := by
  let prefixCertificate :=
    BoundedMachineStackTransformPrefixEmitter.computableInPolyTime
      (tm := tm) selected stack transform
  let tailCertificate := runTailComputableInPolyTime (tm := tm)
    selected stack transform
  let complete := TM2CompositionMachine.computableInPolyTime
    prefixCertificate tailCertificate
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      runTail (tm := tm) selected stack transform
        (BoundedMachineStackTransformPrefixEmitter.run (tm := tm)
          selected stack transform workspace))
  exact complete

end BoundedMachineStackTransformCellEmitter
end PeriodicCNF
end LeanTrominoes
