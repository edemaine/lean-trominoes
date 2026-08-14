/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFCappedRegimeConditionalEmitter
import LeanTrominoes.PeriodicCNFMachineStatementPathRangeEmitter
import LeanTrominoes.PeriodicCNFMachineProgramStatementPathStability

/-!
# Runtime-width statement-path disjunction emission

For every capped width regime, run the fixed terminal-path disjunction in a
nested workspace and retain its new tokens only in that regime.  Exactly one
regime is active.  Width stabilization then identifies the retained word with
the actual runtime `statementPathsProgram`.
-/

noncomputable section

namespace LeanTrominoes

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace PeriodicCNF
namespace BoundedMachineStatementPathsEmitter

open AffineEmitterPipeline
open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Workspace (Data : Type) := AffineEmitterPipeline.Workspace Data
abbrev NestedWorkspace (Data : Type) := Workspace (Workspace Data)
abbrev Path := BoundedMachineProgram.StatementProgramPath tm

def cutoff (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  BoundedMachineProgram.statementWidthCutoff statement

def pathsAt (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regime : Nat) : List (Path (tm := tm)) :=
  BoundedMachineProgram.statementProgramPaths (tm := tm) (space := regime)
    statement control BoundedMachineAtom.identityStackTransforms

def nestedDataSelected {Data : Type} (selected : Data → Bool) :
    Workspace Data → Bool :=
  AffineTemplateEmitterMachine.dataSelected selected

def branchRun {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regime : Nat) :
    List (NestedWorkspace Data) → List (NestedWorkspace Data) :=
  BoundedMachineStatementPathRangeEmitter.run (tm := tm)
    (nestedDataSelected selected) (pathsAt (tm := tm) statement control regime)

def branchTokens
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regime space : Nat) : List Token :=
  BoundedMachineStatementPathRangeEmitter.emitted (tm := tm)
    (pathsAt (tm := tm) statement control regime) space

def conditionalRun {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regime : Nat)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  CappedRegimeConditionalEmitter.run selected (cutoff statement) regime
    (branchRun (tm := tm) selected statement control regime) workspace

theorem conditionalRun_eq_if {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regime : Nat)
    (workspace : List (Workspace Data)) :
    conditionalRun (tm := tm) selected statement control regime workspace =
      if min (AffineTemplateEmitterMachine.selectedCount selected workspace)
          (cutoff statement) = regime then
        workspace ++
          (branchTokens (tm := tm) statement control regime
            (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
              fun token => (Sum.inr token : Workspace Data)
      else workspace := by
  unfold conditionalRun
  apply CappedRegimeConditionalEmitter.run_eq_if
    (branchTokens := branchTokens (tm := tm) statement control regime)
  unfold branchRun branchTokens
  rw [BoundedMachineStatementPathRangeEmitter.run_eq_append]
  rw [AffineEmitterPipeline.selectedCount_embedData]
  rfl

@[simp]
theorem selectedCount_conditionalRun {Data : Type}
    (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regime : Nat)
    (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (conditionalRun (tm := tm) selected statement control regime
          workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  rw [conditionalRun_eq_if]
  split
  · rw [AffineEmitterPipeline.selectedCount_append,
      AffineEmitterPipeline.selectedCount_map_inr, Nat.add_zero]
  · rfl

noncomputable def conditionalRunComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regime : Nat) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (conditionalRun (tm := tm) selected statement control regime) :=
  CappedRegimeConditionalEmitter.computableInPolyTime selected
    (cutoff statement) regime
    (branchRun (tm := tm) selected statement control regime)
    (BoundedMachineStatementPathRangeEmitter.computableInPolyTime
      (tm := tm) (nestedDataSelected selected)
      (pathsAt (tm := tm) statement control regime))

def regimeTokens
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regimes : List Nat) (space : Nat) : List Token :=
  regimes.flatMap fun regime =>
    if min space (cutoff statement) = regime then
      branchTokens (tm := tm) statement control regime space
    else []

def runRegimes {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) :
    List Nat → List (Workspace Data) → List (Workspace Data)
  | [], workspace => workspace
  | regime :: regimes, workspace =>
      runRegimes selected statement control regimes
        (conditionalRun (tm := tm) selected statement control regime workspace)

@[simp]
theorem selectedCount_runRegimes {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regimes : List Nat)
    (workspace : List (Workspace Data)) :
    AffineTemplateEmitterMachine.selectedCount selected
        (runRegimes (tm := tm) selected statement control regimes workspace) =
      AffineTemplateEmitterMachine.selectedCount selected workspace := by
  induction regimes generalizing workspace with
  | nil => rfl
  | cons regime regimes induction =>
      rw [runRegimes, induction, selectedCount_conditionalRun]

theorem runRegimes_eq_append {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (regimes : List Nat)
    (workspace : List (Workspace Data)) :
    runRegimes (tm := tm) selected statement control regimes workspace =
      workspace ++
        (regimeTokens (tm := tm) statement control regimes
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  induction regimes generalizing workspace with
  | nil => simp [runRegimes, regimeTokens]
  | cons regime regimes induction =>
      let space :=
        AffineTemplateEmitterMachine.selectedCount selected workspace
      let first := conditionalRun (tm := tm) selected statement control
        regime workspace
      have firstEq : first =
          if min space (cutoff statement) = regime then
            workspace ++
              (branchTokens (tm := tm) statement control regime space).map
                fun token => (Sum.inr token : Workspace Data)
          else workspace := by
        exact conditionalRun_eq_if (tm := tm) selected statement control
          regime workspace
      have spaceEq :
          AffineTemplateEmitterMachine.selectedCount selected first =
            space := by
        unfold first
        rw [selectedCount_conditionalRun]
      rw [runRegimes]
      change runRegimes (tm := tm) selected statement control regimes first = _
      rw [induction, spaceEq, firstEq]
      unfold regimeTokens space
      by_cases active : min
          (AffineTemplateEmitterMachine.selectedCount selected workspace)
            (cutoff statement) = regime
      · simp [active, List.map_append, List.append_assoc]
      · simp [active]

noncomputable def runRegimesComputableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) :
    (regimes : List Nat) →
      @TM2ComputableInPolyTime
        (List (Workspace Data)) (List (Workspace Data))
        (Workspace Data) (Workspace Data) id id
        (runRegimes (tm := tm) selected statement control regimes)
  | [] => AffineEmitterPipeline.identityComputableInPolyTime
  | regime :: regimes => by
      let complete := TM2CompositionMachine.computableInPolyTime
        (conditionalRunComputableInPolyTime (tm := tm)
          selected statement control regime)
        (runRegimesComputableInPolyTime selected statement control regimes)
      simpa only [runRegimes] using complete

theorem flatMap_ite_eq_nil_of_not_mem {Target : Type}
    (active : Nat) (values : List Nat) (tokens : Nat → List Target)
    (notMem : active ∉ values) :
    values.flatMap (fun value =>
      if active = value then tokens value else []) = [] := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      have different : active ≠ value := by
        intro equal
        apply notMem
        simp [equal]
      have notMemTail : active ∉ values := by
        intro member
        exact notMem (by simp [member])
      simp [different, induction notMemTail]

theorem flatMap_ite_eq_of_mem_nodup {Target : Type}
    (active : Nat) (values : List Nat) (tokens : Nat → List Target)
    (member : active ∈ values) (nodup : values.Nodup) :
    values.flatMap (fun value =>
      if active = value then tokens value else []) = tokens active := by
  induction values with
  | nil => simp at member
  | cons value values induction =>
      rw [List.nodup_cons] at nodup
      by_cases same : active = value
      · subst value
        have tailEmpty := flatMap_ite_eq_nil_of_not_mem
          active values tokens nodup.1
        simp [tailEmpty]
      · have tailMember : active ∈ values := by
          simpa [same] using member
        simp [same, induction tailMember nodup.2]

def regimes (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : List Nat :=
  List.range (cutoff statement + 1)

def emitted
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (space : Nat) : List Token :=
  branchTokens (tm := tm) statement control
    (min space (cutoff statement)) space

def run {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) :
    List (Workspace Data) → List (Workspace Data) :=
  runRegimes (tm := tm) selected statement control (regimes statement)

theorem run_eq_append {Data : Type} (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (workspace : List (Workspace Data)) :
    run (tm := tm) selected statement control workspace =
      workspace ++
        (emitted (tm := tm) statement control
          (AffineTemplateEmitterMachine.selectedCount selected workspace)).map
            fun token => (Sum.inr token : Workspace Data) := by
  unfold run
  rw [runRegimes_eq_append]
  unfold regimeTokens emitted regimes
  let space := AffineTemplateEmitterMachine.selectedCount selected workspace
  let active := min space (cutoff statement)
  have activeLt : active < cutoff statement + 1 := by
    unfold active
    omega
  have member : active ∈ List.range (cutoff statement + 1) :=
    List.mem_range.mpr activeLt
  have unique := flatMap_ite_eq_of_mem_nodup active
    (List.range (cutoff statement + 1))
    (fun regime => branchTokens (tm := tm) statement control regime space)
    member List.nodup_range
  simpa only [space, active] using congrArg
    (fun tokens => workspace ++ tokens.map fun token =>
      (Sum.inr token : Workspace Data)) unique

noncomputable def computableInPolyTime {Data : Type}
    [Fintype Data] [Inhabited Data] (selected : Data → Bool)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) :
    @TM2ComputableInPolyTime
      (List (Workspace Data)) (List (Workspace Data))
      (Workspace Data) (Workspace Data) id id
      (run (tm := tm) selected statement control) :=
  runRegimesComputableInPolyTime (tm := tm) selected statement control
    (regimes statement)

/-- The retained unique regime is exactly the actual runtime path
disjunction. -/
theorem emitted_eq_statementPathsProgram
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) (space : Nat) :
    emitted (tm := tm) statement control space =
      ofProgram
        (BoundedMachineProgram.statementPathsProgram (tm := tm)
          (space := space) statement control
          BoundedMachineAtom.identityStackTransforms) := by
  unfold emitted branchTokens pathsAt cutoff
  rw [BoundedMachineStatementPathRangeEmitter.emitted_eq_anyPrograms]
  unfold BoundedMachineProgram.statementPathsProgram
  rw [← BoundedMachineProgram.statementProgramPaths_eq_capped]

end BoundedMachineStatementPathsEmitter
end PeriodicCNF
end LeanTrominoes
