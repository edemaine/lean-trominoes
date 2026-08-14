/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFixedMarkerThresholdEmitter
import LeanTrominoes.PeriodicCNFMachineBivariateStackTemplates

/-!
# Bounded stack-transform fit emission

Emit the one fit operand preceding a normalized stack transform.  A sentinel
below the pushed-prefix length emits `false`.  At or above that length, the
complementary sentinel emits either the first omitted-source-cell test or
`true`, according to the transform's fixed discard count.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStackTransformFitsEmitter

open AffineEmitterPipeline
open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data

def cutoff {stack : tm.K} (transform : StackTransform (tm.Γ stack)) : Nat :=
  transform.added.length

def belowProgram : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.constant false

def atProgram (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    BivariateProgramTemplates.Program :=
  if transform.discard < transform.added.length then
    BoundedMachineBivariateStack.currentStackCellIs (tm := tm) stack
      transform.discard none
  else
    BivariateProgramTemplates.constant true

def belowTokens {stack : tm.K} (transform : StackTransform (tm.Γ stack))
    (space : Nat) : List Token :=
  FixedMarkerThresholdEmitter.emittedBelow belowProgram.recipes
    (cutoff transform) space

def atTokens (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (space : Nat) : List Token :=
  FixedMarkerThresholdEmitter.emittedAt
    (atProgram (tm := tm) stack transform).recipes (cutoff transform) space

def emitted (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (space : Nat) : List Token :=
  belowTokens (tm := tm) transform space ++
    atTokens (tm := tm) stack transform space

def runBelow {Data : Type} {stack : tm.K} (selected : Data → Bool)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  FixedMarkerThresholdEmitter.runBelow selected (cutoff transform)
    belowProgram.recipes workspace

def runAt {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  FixedMarkerThresholdEmitter.runAt selected (cutoff transform)
    (atProgram (tm := tm) stack transform).recipes workspace

def run {Data : Type} (selected : Data → Bool) (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  runAt (tm := tm) selected stack transform
    (runBelow (tm := tm) selected transform workspace)

omit stackFinite in
@[simp]
theorem selectedCount_runBelow {Data : Type} {stack : tm.K}
    (selected : Data → Bool)
    (transform : StackTransform (tm.Γ stack))
    (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (runBelow (tm := tm) selected transform workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  unfold runBelow
  rw [FixedMarkerThresholdEmitter.runBelow_eq_append,
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
  unfold run runAt
  rw [FixedMarkerThresholdEmitter.runAt_eq_append,
    selectedCount_runBelow]
  unfold runBelow
  rw [FixedMarkerThresholdEmitter.runBelow_eq_append]
  unfold emitted belowTokens atTokens
  simp [List.map_append, List.append_assoc]

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected stack transform) := by
  let belowCertificate :=
    FixedMarkerThresholdEmitter.runBelowComputableInPolyTime
      selected (cutoff transform) belowProgram.recipes
  let atCertificate :=
    FixedMarkerThresholdEmitter.runAtComputableInPolyTime
      selected (cutoff transform)
        (atProgram (tm := tm) stack transform).recipes
  let complete := TM2CompositionMachine.computableInPolyTime
    belowCertificate atCertificate
  change @TM2ComputableInPolyTime
    (List (Workspace Data)) (List (Workspace Data))
    (Workspace Data) (Workspace Data) id id
    (fun workspace =>
      runAt (tm := tm) selected stack transform
        (runBelow (tm := tm) selected transform workspace))
  exact complete

theorem evaluate_atProgram (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat)
    (addedFits : transform.added.length ≤ space) :
    (atProgram (tm := tm) stack transform).evaluate
        (space - transform.added.length) 0 =
      BoundedMachineProgram.stackTransformFits (tm := tm) (space := space)
        stack transform := by
  by_cases discardLt : transform.discard < transform.added.length
  · have omittedArithmetic :
        space - transform.added.length + transform.discard < space := by
      omega
    simp only [atProgram, discardLt, if_pos,
      BoundedMachineBivariateStack.evaluate_currentStackCellIs,
      BoundedMachineProgram.stackTransformFits, addedFits, dif_pos,
      StackTransform.firstOmitted, omittedArithmetic]
    have positionEq :
        transform.discard + (space - transform.added.length) + 0 =
          space - transform.added.length + transform.discard := by
      omega
    rw [positionEq]
  · have omittedArithmetic :
        ¬space - transform.added.length + transform.discard < space := by
      omega
    simp [atProgram, discardLt,
      BoundedMachineProgram.stackTransformFits, addedFits,
      StackTransform.firstOmitted, omittedArithmetic]

/-- The two complementary conditional passes emit exactly the single
normalized fit operand for every runtime width. -/
theorem emitted_eq_stackTransformFits (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (space : Nat) :
    emitted (tm := tm) stack transform space =
      ofProgram
        (BoundedMachineProgram.stackTransformFits (tm := tm) (space := space)
          stack transform) := by
  by_cases addedFits : transform.added.length ≤ space
  · have notBelow : ¬space < transform.added.length :=
      Nat.not_lt_of_ge addedFits
    unfold emitted belowTokens atTokens
    rw [show cutoff transform = transform.added.length by rfl]
    simp only [FixedMarkerThresholdEmitter.emittedBelow,
      FixedMarkerThresholdEmitter.emittedAt, notBelow, if_false,
      addedFits, if_true,
      BivariateTemplateEmitterMachine.positionRangeTokens_zero,
      List.nil_append,
      BivariateTemplateEmitterMachine.positionRangeTokens_succ,
      Nat.zero_add,
      BivariateTemplateEmitterMachine.positionTokens,
      BivariateProgramTemplates.Program.positionTokens_recipes,
      List.append_nil]
    rw [evaluate_atProgram (tm := tm) stack transform space addedFits]
  · have below : space < transform.added.length :=
      Nat.lt_of_not_ge addedFits
    unfold emitted belowTokens atTokens belowProgram
    rw [show cutoff transform = transform.added.length by rfl]
    simp [FixedMarkerThresholdEmitter.emittedBelow,
      FixedMarkerThresholdEmitter.emittedAt, below, addedFits,
      BivariateTemplateEmitterMachine.positionRangeTokens,
      BivariateTemplateEmitterMachine.positionTokens,
      BoundedMachineProgram.stackTransformFits]

end BoundedMachineStackTransformFitsEmitter
end PeriodicCNF
end LeanTrominoes
