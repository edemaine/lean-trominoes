/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineBivariateStackTemplates
import LeanTrominoes.PeriodicCNFMachineAffineStackTemplates

/-!
# Pushed-prefix and shifted-interior stack-transform emission

For one normalized stack transform, emit every represented pushed cell and
then every source/target equality whose source remains represented.  A capped
prefix mark makes each fixed pushed position conditional on the runtime width;
the suffix after `max(added.length, discard)` drives the affine equality loop.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStackTransformPrefixEmitter

open AffineEmitterPipeline
open AffineProgramTemplates
open SelectedPrefixMarkerMachine
open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def workspaceSelected {Data : Type} (selected : Data → Bool) :
    Workspace Data → Bool :=
  AffineTemplateEmitterMachine.dataSelected selected

def cutoff {stack : tm.K} (transform : StackTransform (tm.Γ stack)) : Nat :=
  max transform.added.length transform.discard

def addedPhase {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (position : Fin transform.added.length) :
    Phase (SelectedPrefixMarkerMachine.Tagged (cutoff transform)
      (Workspace Data)) :=
  BoundedMachineOneHotEmitter.affinePhase
    (atPrefix (workspaceSelected selected) position.val)
    (BoundedMachineAffineProgram.nextStackCellIs (tm := tm) stack
      position.val (some transform.added[position]))

def equalityPhase {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    Phase (SelectedPrefixMarkerMachine.Tagged (cutoff transform)
      (Workspace Data)) :=
  BoundedMachineOneHotEmitter.affinePhase
    (afterPrefix (workspaceSelected selected) (cutoff transform))
    (BoundedMachineAffineProgram.stackCellsEqual (tm := tm) stack
      transform.discard transform.added.length)

def phases {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    List (Phase (SelectedPrefixMarkerMachine.Tagged (cutoff transform)
      (Workspace Data))) :=
  (List.finRange transform.added.length).map
      (addedPhase (tm := tm) selected stack transform) ++
    [equalityPhase (tm := tm) selected stack transform]

def addedTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : List Token :=
  (List.finRange transform.added.length).flatMap fun position =>
    if position.val < space then
      ofProgram
        (BoundedMachineProgram.nextStackCellIs (tm := tm) stack position.val
          (some transform.added[position]))
    else []

def equalityTokens (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) : List Token :=
  (List.range (space - cutoff transform)).flatMap fun position =>
    ofProgram
      (BoundedMachineProgram.stackCellsEqual (tm := tm) stack
        (position + transform.discard)
        (position + transform.added.length))

def emitted (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (space : Nat) : List Token :=
  addedTokens (tm := tm) stack transform space ++
    equalityTokens (tm := tm) stack transform space

theorem addedPhase_emitted {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (position : Fin transform.added.length)
    (workspace : List (Workspace Data)) :
    (addedPhase (tm := tm) selected stack transform position).emitted
        (mark (workspaceSelected selected) (cutoff transform) workspace) =
      if position.val <
          AffineTemplateEmitterMachine.selectedCount selected workspace then
        ofProgram
          (BoundedMachineProgram.nextStackCellIs (tm := tm) stack position.val
            (some transform.added[position]))
      else [] := by
  let space := AffineTemplateEmitterMachine.selectedCount selected workspace
  have positionLe : position.val + 1 ≤ cutoff transform := by
    unfold cutoff
    have positionLt := position.isLt
    omega
  have countEq := selectedCount_atPrefix_mark
    (workspaceSelected selected) positionLe workspace
  change UnaryPolynomialPaddingMachine.selectedCount
      (atPrefix (workspaceSelected selected) position.val)
      (mark (workspaceSelected selected) (cutoff transform) workspace) =
        (if position.val < space then 1 else 0) at countEq
  unfold addedPhase
  by_cases represented : position.val < space
  · rw [BoundedMachineOneHotEmitter.affinePhase_emitted
      (atPrefix (workspaceSelected selected) position.val) _ _ 1]
    · have represented' : position.val <
          AffineTemplateEmitterMachine.selectedCount selected workspace := by
        simpa [space] using represented
      simp [represented',
        BoundedMachineAffineProgram.evaluate_nextStackCellIs]
    · simpa [represented] using countEq
  · rw [BoundedMachineOneHotEmitter.affinePhase_emitted
      (atPrefix (workspaceSelected selected) position.val) _ _ 0]
    · have represented' : ¬ position.val <
          AffineTemplateEmitterMachine.selectedCount selected workspace := by
        simpa [space] using represented
      simp [represented']
    · simpa [represented] using countEq

theorem equalityPhase_emitted {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    (equalityPhase (tm := tm) selected stack transform).emitted
        (mark (workspaceSelected selected) (cutoff transform) workspace) =
      equalityTokens (tm := tm) stack transform
        (AffineTemplateEmitterMachine.selectedCount selected workspace) := by
  let space := AffineTemplateEmitterMachine.selectedCount selected workspace
  have countEq := selectedCount_afterPrefix_mark
    (workspaceSelected selected) (skip := cutoff transform)
      (Nat.le_refl (cutoff transform)) workspace
  change UnaryPolynomialPaddingMachine.selectedCount
      (afterPrefix (workspaceSelected selected) (cutoff transform))
      (mark (workspaceSelected selected) (cutoff transform) workspace) =
        space - cutoff transform at countEq
  unfold equalityPhase
  rw [BoundedMachineOneHotEmitter.affinePhase_emitted
    (afterPrefix (workspaceSelected selected) (cutoff transform)) _ _
      (space - cutoff transform) countEq]
  rw [BoundedMachineOneHotEmitter.positions_zero_eq_range]
  unfold equalityTokens
  apply List.flatMap_congr
  intro position _
  rw [BoundedMachineAffineProgram.evaluate_stackCellsEqual]

theorem emittedAll_addedPhases {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    AffineEmitterPipeline.emittedAll
        ((List.finRange transform.added.length).map
          (addedPhase (tm := tm) selected stack transform))
        (mark (workspaceSelected selected) (cutoff transform) workspace) =
      addedTokens (tm := tm) stack transform
        (AffineTemplateEmitterMachine.selectedCount selected workspace) := by
  rw [BoundedMachineOneHotEmitter.emittedAll_map]
  unfold addedTokens
  apply List.flatMap_congr
  intro position _
  exact addedPhase_emitted selected stack transform position workspace

theorem emittedAll_phases {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    AffineEmitterPipeline.emittedAll
        (phases (tm := tm) selected stack transform)
        (mark (workspaceSelected selected) (cutoff transform) workspace) =
      emitted (tm := tm) stack transform
        (AffineTemplateEmitterMachine.selectedCount selected workspace) := by
  unfold phases emitted
  rw [BoundedMachineOneHotEmitter.emittedAll_append,
    emittedAll_addedPhases]
  simp only [AffineEmitterPipeline.emittedAll, List.append_nil]
  rw [equalityPhase_emitted]

def run {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  MarkedAffineEmitterPipeline.run (workspaceSelected selected)
    (cutoff transform) (phases (tm := tm) selected stack transform) workspace

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    run (tm := tm) selected stack transform workspace =
      workspace ++
        (emitted (tm := tm) stack transform
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [MarkedAffineEmitterPipeline.run_eq_append, emittedAll_phases]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected stack transform) :=
  MarkedAffineEmitterPipeline.computableInPolyTime
    (workspaceSelected selected) (cutoff transform)
    (phases (tm := tm) selected stack transform)

end BoundedMachineStackTransformPrefixEmitter
end PeriodicCNF
end LeanTrominoes
