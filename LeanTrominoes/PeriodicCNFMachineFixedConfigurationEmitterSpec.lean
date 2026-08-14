/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineWellFormedEmitterSpec

/-!
# Concrete emitter schedule for a fixed bounded configuration

For each stack, the finite occupied prefix of a fixed configuration is emitted
literally.  A selected-prefix tag then skips that many space markers and an
affine phase emits the remaining `none` cells.  This file proves that the
resulting fixed schedule is exactly the normalized `currentConfigIs` or
`nextConfigIs` postorder program at every runtime width in which the fixed
configuration fits.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineFixedConfigurationEmitter

open BoundedMachineAtom
open AffineEmitterPipeline
open AffineProgramTemplates
open UnaryProgramTokens
open UnaryProgramTokenAlgebra
open SelectedPrefixMarkerMachine
open BoundedMachineOneHotEmitter

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Marked (cutoff : Nat) (Data : Type) := Tagged cutoff Data

/-- One normalized fixed-label test, on either time slice. -/
def labelIs (slice : TransitionSlice) (label : Option tm.Λ) :
    TransitionProgram.Program :=
  match slice with
  | .current => BoundedMachineProgram.currentLabelIs label
  | .next => BoundedMachineProgram.nextLabelIs label

/-- One normalized fixed-control test, on either time slice. -/
def controlIs (slice : TransitionSlice) (control : tm.σ) :
    TransitionProgram.Program :=
  match slice with
  | .current => BoundedMachineProgram.currentControlIs control
  | .next => BoundedMachineProgram.nextControlIs control

/-- One normalized fixed stack-cell test, on either time slice. -/
def stackCellIs (slice : TransitionSlice) (stack : tm.K) (position : Nat)
    (symbol : Option (tm.Γ stack)) : TransitionProgram.Program :=
  match slice with
  | .current =>
      BoundedMachineProgram.currentStackCellIs stack position symbol
  | .next =>
      BoundedMachineProgram.nextStackCellIs stack position symbol

/-- Test one complete fixed stack, on either time slice. -/
def stackIs (slice : TransitionSlice) (target : tm.Cfg) (stack : tm.K)
    (space : Nat) : TransitionProgram.Program :=
  TransitionProgram.all ((List.finRange space).map fun position =>
    stackCellIs (tm := tm) slice stack position.val
      (target.stk stack)[position.val]?)

/-- Test one complete fixed configuration, on either time slice. -/
def configurationIs (slice : TransitionSlice) (target : tm.Cfg)
    (space : Nat) : TransitionProgram.Program :=
  TransitionProgram.conjoin (labelIs (tm := tm) slice target.l)
    (TransitionProgram.conjoin (controlIs (tm := tm) slice target.var)
      (TransitionProgram.all ((finiteValues tm.K).map fun stack =>
        stackIs (tm := tm) slice target stack space)))

@[simp]
theorem stackIs_current (target : tm.Cfg) (stack : tm.K) (space : Nat) :
    stackIs (tm := tm) .current target stack space =
      BoundedMachineProgram.currentStackIs (tm := tm) (space := space)
        target stack := by
  rfl

@[simp]
theorem stackIs_next (target : tm.Cfg) (stack : tm.K) (space : Nat) :
    stackIs (tm := tm) .next target stack space =
      BoundedMachineProgram.nextStackIs (tm := tm) (space := space)
        target stack := by
  rfl

@[simp]
theorem configurationIs_current (target : tm.Cfg) (space : Nat) :
    configurationIs (tm := tm) .current target space =
      BoundedMachineProgram.currentConfigIs (tm := tm) (space := space)
        target := by
  rfl

@[simp]
theorem configurationIs_next (target : tm.Cfg) (space : Nat) :
    configurationIs (tm := tm) .next target space =
      BoundedMachineProgram.nextConfigIs (tm := tm) (space := space)
        target := by
  rfl

/-- Affine tail template beginning immediately after a fixed stack prefix. -/
def stackTailProgram (slice : TransitionSlice) (stack : tm.K)
    (prefixLength : Nat) : AffineProgramTemplates.Program :=
  match slice with
  | .current =>
      BoundedMachineAffineProgram.currentStackCellIs
        (tm := tm) stack prefixLength none
  | .next =>
      BoundedMachineAffineProgram.nextStackCellIs
        (tm := tm) stack prefixLength none

@[simp]
theorem evaluate_stackTailProgram (slice : TransitionSlice)
    (stack : tm.K) (prefixLength position : Nat) :
    (stackTailProgram (tm := tm) slice stack prefixLength).evaluate
        position =
      stackCellIs (tm := tm) slice stack (position + prefixLength) none := by
  cases slice <;> simp [stackTailProgram, stackCellIs]

/-- Literal token prefix for the occupied cells of one fixed stack. -/
def stackPrefixTokens (slice : TransitionSlice) (target : tm.Cfg)
    (stack : tm.K) : List Token :=
  (List.range (target.stk stack).length).flatMap fun position =>
    ofProgram (stackCellIs (tm := tm) slice stack position
      (target.stk stack)[position]?)

def tailSelector {Data : Type} {cutoff : Nat} (selected : Data → Bool)
    (target : tm.Cfg) (stack : tm.K) : Marked cutoff Data → Bool :=
  afterPrefix selected (target.stk stack).length

def stackTailPhase {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (slice : TransitionSlice)
    (target : tm.Cfg) (stack : tm.K) : Phase (Marked cutoff Data) :=
  affinePhase (tailSelector selected target stack)
    (stackTailProgram (tm := tm) slice stack (target.stk stack).length)

def stackTailConjoinPhase {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) (target : tm.Cfg)
    (stack : tm.K) : Phase (Marked cutoff Data) :=
  conjoinPhase (tailSelector selected target stack)

/-- Complete fixed phase schedule for one fixed stack. -/
def stackPhases {Data : Type} {cutoff : Nat} (selected : Data → Bool)
    (slice : TransitionSlice) (target : tm.Cfg) (stack : tm.K) :
    List (Phase (Marked cutoff Data)) :=
  [fixedPhase (stackPrefixTokens (tm := tm) slice target stack),
    stackTailPhase (tm := tm) selected slice target stack,
    fixedPhase (allEnding (target.stk stack).length),
    stackTailConjoinPhase (tm := tm) selected target stack]

/-- Complete fixed phase schedule for one fixed configuration. -/
def phases {Data : Type} {cutoff : Nat} (selected : Data → Bool)
    (slice : TransitionSlice) (target : tm.Cfg) :
    List (Phase (Marked cutoff Data)) :=
  [fixedPhase
      (ofProgram (labelIs (tm := tm) slice target.l) ++
        ofProgram (controlIs (tm := tm) slice target.var))] ++
    ((finiteValues tm.K).flatMap fun stack =>
      stackPhases (tm := tm) selected slice target stack) ++
    [fixedPhase
      (allEnding (Fintype.card tm.K) ++
        instructionTokens .conjoin ++ instructionTokens .conjoin)]

theorem range_add_split (start tail : Nat) :
    List.range (start + tail) =
      List.range start ++
        (List.range tail).map fun offset => start + offset := by
  induction tail with
  | zero => simp
  | succ tail induction =>
      rw [Nat.add_succ, List.range_succ, induction, List.range_succ,
        List.map_append]
      simp [List.append_assoc]

theorem range_split {start total : Nat} (fit : start ≤ total) :
    List.range total =
      List.range start ++
        (List.range (total - start)).map fun offset => start + offset := by
  conv_lhs => rw [show total = start + (total - start) by omega]
  exact range_add_split start (total - start)

omit stackFinite in
theorem tailSelector_count {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (target : tm.Cfg) (stack : tm.K)
    (prefixFitsCutoff : (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    UnaryPolynomialPaddingMachine.selectedCount
        (tailSelector selected target stack)
        (mark selected cutoff data) =
      space - (target.stk stack).length := by
  rw [tailSelector, selectedCount_afterPrefix_mark selected prefixFitsCutoff,
    spaceEq]

theorem stackTailPhase_emitted {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (slice : TransitionSlice) (target : tm.Cfg)
    (stack : tm.K)
    (prefixFitsCutoff : (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    (stackTailPhase (tm := tm) selected slice target stack).emitted
        (mark selected cutoff data) =
      (List.range (space - (target.stk stack).length)).flatMap
        fun offset =>
          ofProgram (stackCellIs (tm := tm) slice stack
            ((target.stk stack).length + offset) none) := by
  rw [stackTailPhase,
    affinePhase_emitted (tailSelector selected target stack) _
      (mark selected cutoff data)
      (space - (target.stk stack).length)]
  · rw [positions_zero_eq_range]
    apply List.flatMap_congr
    intro position _
    rw [evaluate_stackTailProgram]
    congr 2
    omega
  · exact tailSelector_count selected target stack prefixFitsCutoff data
      space spaceEq

omit stackFinite in
theorem stackTailConjoinPhase_emitted {Data : Type}
    (selected : Data → Bool) {cutoff : Nat} (target : tm.Cfg)
    (stack : tm.K)
    (prefixFitsCutoff : (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    (stackTailConjoinPhase (tm := tm) selected target stack).emitted
        (mark selected cutoff data) =
      repeatInstructionTokens .conjoin
        (space - (target.stk stack).length) := by
  unfold stackTailConjoinPhase
  apply conjoinPhase_emitted
  exact tailSelector_count selected target stack prefixFitsCutoff data
    space spaceEq

theorem stackOperandTokens_split (slice : TransitionSlice)
    (target : tm.Cfg) (stack : tm.K) (space : Nat)
    (prefixFitsSpace : (target.stk stack).length ≤ space) :
    ((List.finRange space).map fun position =>
        stackCellIs (tm := tm) slice stack position.val
          (target.stk stack)[position.val]?).flatMap ofProgram =
      stackPrefixTokens (tm := tm) slice target stack ++
        (List.range (space - (target.stk stack).length)).flatMap
          fun offset =>
            ofProgram (stackCellIs (tm := tm) slice stack
              ((target.stk stack).length + offset) none) := by
  rw [List.flatMap_map]
  change (List.finRange space).flatMap
      (fun position => ofProgram (stackCellIs (tm := tm) slice stack
        position.val (target.stk stack)[position.val]?)) = _
  calc
    _ = ((List.finRange space).map Fin.val).flatMap
          (fun position => ofProgram (stackCellIs (tm := tm) slice stack
            position (target.stk stack)[position]?)) := by
        rw [List.flatMap_map]
    _ = (List.range space).flatMap
          (fun position => ofProgram (stackCellIs (tm := tm) slice stack
            position (target.stk stack)[position]?)) := by
        rw [BoundedMachineOneHotEmitter.finRange_values]
    _ = _ := by
      rw [range_split prefixFitsSpace, List.flatMap_append,
        List.flatMap_map]
      unfold stackPrefixTokens
      congr 1
      apply List.flatMap_congr
      intro offset _
      rw [List.getElem?_eq_none]
      omega

theorem emittedAll_stackPhases {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (slice : TransitionSlice) (target : tm.Cfg)
    (stack : tm.K)
    (prefixFitsCutoff : (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (prefixFitsSpace : (target.stk stack).length ≤ space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll (stackPhases (tm := tm) selected slice target stack)
        (mark selected cutoff data) =
      ofProgram (stackIs (tm := tm) slice target stack space) := by
  have ending : allEnding space =
      allEnding (target.stk stack).length ++
        repeatInstructionTokens .conjoin
          (space - (target.stk stack).length) := by
    calc
      allEnding space = allEnding ((target.stk stack).length +
          (space - (target.stk stack).length)) := by congr 1; omega
      _ = _ := by
        simpa [allEnding] using
          foldEnding_add true .conjoin (target.stk stack).length
            (space - (target.stk stack).length)
  unfold stackPhases
  simp only [emittedAll, List.append_nil]
  rw [fixedPhase_emitted,
    stackTailPhase_emitted selected slice target stack prefixFitsCutoff data
      space spaceEq,
    fixedPhase_emitted,
    stackTailConjoinPhase_emitted selected target stack prefixFitsCutoff data
      space spaceEq]
  unfold stackIs
  rw [ofProgram_all, List.length_map, List.length_finRange,
    stackOperandTokens_split slice target stack space prefixFitsSpace,
    ending]
  ac_rfl

theorem emittedAll_flatMap_stackPhases {Data : Type}
    (selected : Data → Bool) {cutoff : Nat} (slice : TransitionSlice)
    (target : tm.Cfg)
    (prefixFitsCutoff : ∀ stack, (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (prefixFitsSpace : ∀ stack, (target.stk stack).length ≤ space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll
        ((finiteValues tm.K).flatMap fun stack =>
          stackPhases (tm := tm) selected slice target stack)
        (mark selected cutoff data) =
      ((finiteValues tm.K).map fun stack =>
        stackIs (tm := tm) slice target stack space).flatMap ofProgram := by
  rw [BoundedMachineWellFormedEmitter.emittedAll_flatMap]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro stack _
  exact emittedAll_stackPhases selected slice target stack
    (prefixFitsCutoff stack) data space (prefixFitsSpace stack) spaceEq

/-- The fixed phase schedule emits the exact complete configuration test. -/
theorem emittedAll_phases {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (slice : TransitionSlice) (target : tm.Cfg)
    (prefixFitsCutoff : ∀ stack, (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (prefixFitsSpace : ∀ stack, (target.stk stack).length ≤ space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll (phases (tm := tm) selected slice target)
        (mark selected cutoff data) =
      ofProgram (configurationIs (tm := tm) slice target space) := by
  have stackOutput := emittedAll_flatMap_stackPhases selected slice target
    prefixFitsCutoff data space prefixFitsSpace spaceEq
  unfold phases
  rw [emittedAll_append, emittedAll_append]
  simp only [emittedAll, fixedPhase_emitted, List.append_nil]
  rw [stackOutput]
  unfold configurationIs
  rw [ofProgram_conjoin, ofProgram_conjoin, ofProgram_all,
    List.length_map, finiteValues_length]
  ac_rfl

/-- Current-slice specialization used for the accepting endpoint. -/
theorem emittedAll_currentPhases {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (target : tm.Cfg)
    (prefixFitsCutoff : ∀ stack, (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (prefixFitsSpace : ∀ stack, (target.stk stack).length ≤ space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll (phases (tm := tm) selected .current target)
        (mark selected cutoff data) =
      ofProgram (BoundedMachineProgram.currentConfigIs (tm := tm)
        (space := space) target) := by
  simpa using emittedAll_phases selected .current target prefixFitsCutoff data
    space prefixFitsSpace spaceEq

/-- Next-slice specialization used for a fixed reset endpoint. -/
theorem emittedAll_nextPhases {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (target : tm.Cfg)
    (prefixFitsCutoff : ∀ stack, (target.stk stack).length ≤ cutoff)
    (data : List Data) (space : Nat)
    (prefixFitsSpace : ∀ stack, (target.stk stack).length ≤ space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll (phases (tm := tm) selected .next target)
        (mark selected cutoff data) =
      ofProgram (BoundedMachineProgram.nextConfigIs (tm := tm)
        (space := space) target) := by
  simpa using emittedAll_phases selected .next target prefixFitsCutoff data
    space prefixFitsSpace spaceEq

end BoundedMachineFixedConfigurationEmitter
end PeriodicCNF
end LeanTrominoes
