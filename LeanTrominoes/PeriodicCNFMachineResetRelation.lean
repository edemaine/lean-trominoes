/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStatementSemantics

/-!
# Bounded accepting-reset machine relation

This file combines structural well-formedness, the verified ordinary TM2 step,
the fixed-width successor clock, and an accepting reset to a chosen initial
configuration.  The resulting Boolean expression presents exactly the local
reset-clock relation used to turn an accepting computation into a cycle.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Require every represented cell of one current-slice stack to equal the
corresponding cell of a fixed target configuration. -/
def currentStackIs (target : tm.Cfg) (stack : tm.K) : TransitionExpr :=
  TransitionExpr.all ((List.finRange space).map fun position =>
    currentStackCellIs (tm := tm) (clockBits := clockBits) stack position
      (target.stk stack)[position.val]?)

/-- Require the bounded machine configuration in the current slice to equal
a fixed target configuration. -/
def currentConfigIs (target : tm.Cfg) : TransitionExpr :=
  .and
    (currentLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) target.l)
    (.and
      (currentControlIs (tm := tm) (space := space)
        (clockBits := clockBits) target.var)
      (TransitionExpr.all ((finiteValues tm.K).map fun stack =>
        currentStackIs (tm := tm) (space := space)
          (clockBits := clockBits) target stack)))

theorem currentStackIs_encode_iff
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (target : tm.Cfg) (stack : tm.K)
    (currentFits : (current.config.stk stack).length ≤ space)
    (targetFits : (target.stk stack).length ≤ space) :
    (currentStackIs (tm := tm) (space := space) (clockBits := clockBits)
      target stack).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      current.config.stk stack = target.stk stack := by
  rw [currentStackIs, TransitionExpr.all_eval, List.all_eq_true]
  constructor
  · intro cells
    apply List.ext_getElem?
    intro index
    by_cases indexInRange : index < space
    · let position : Fin space := ⟨index, indexInRange⟩
      have cell := cells
        (currentStackCellIs (tm := tm) (clockBits := clockBits) stack position
          (target.stk stack)[position.val]?)
        (List.mem_map.mpr ⟨position, by simp, rfl⟩)
      simpa [currentStackCellIs, TransitionExpr.current,
        TransitionExpr.eval, TransitionWire.value, position] using cell
    · have spaceLe : space ≤ index := Nat.not_lt.mp indexInRange
      rw [List.getElem?_eq_none (le_trans currentFits spaceLe),
        List.getElem?_eq_none (le_trans targetFits spaceLe)]
  · intro stacksEq expression expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    simpa [currentStackCellIs, TransitionExpr.current,
      TransitionExpr.eval, TransitionWire.value, stacksEq]

private theorem current_cfg_eq_of_fields {first second : tm.Cfg}
    (labelEq : first.l = second.l)
    (controlEq : first.var = second.var)
    (stacksEq : ∀ stack, first.stk stack = second.stk stack) :
    first = second := by
  cases first with
  | mk firstLabel firstControl firstStacks =>
    cases second with
    | mk secondLabel secondControl secondStacks =>
      congr 1
      funext stack
      exact stacksEq stack

theorem currentConfigIs_encode_iff
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (target : tm.Cfg)
    (currentFits : ∀ stack, (current.config.stk stack).length ≤ space)
    (targetFits : ∀ stack, (target.stk stack).length ≤ space) :
    (currentConfigIs (tm := tm) (space := space) (clockBits := clockBits)
      target).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      current.config = target := by
  simp only [currentConfigIs, TransitionExpr.eval, Bool.and_eq_true]
  constructor
  · rintro ⟨labelEq, controlEq, stacksTrue⟩
    apply current_cfg_eq_of_fields
    · simpa [currentLabelIs, TransitionExpr.current,
        TransitionExpr.eval, TransitionWire.value] using labelEq
    · simpa [currentControlIs, TransitionExpr.current,
        TransitionExpr.eval, TransitionWire.value] using controlEq
    · intro stack
      apply (currentStackIs_encode_iff current next target stack
        (currentFits stack) (targetFits stack)).mp
      rw [TransitionExpr.all_eval, List.all_eq_true] at stacksTrue
      exact stacksTrue _
        (List.mem_map.mpr ⟨stack, mem_finiteValues stack, rfl⟩)
  · intro configEq
    subst target
    refine ⟨?_, ?_, ?_⟩
    · simp [currentLabelIs, TransitionExpr.current,
        TransitionExpr.eval, TransitionWire.value]
    · simp [currentControlIs, TransitionExpr.current,
        TransitionExpr.eval, TransitionWire.value]
    · rw [TransitionExpr.all_eval, List.all_eq_true]
      intro expression expressionMem
      obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
      exact (currentStackIs_encode_iff current next current.config stack
        (currentFits stack) (currentFits stack)).mpr rfl

theorem currentStackIs_atomsBelow (target : tm.Cfg) (stack : tm.K) :
    (currentStackIs (tm := tm) (space := space) (clockBits := clockBits)
      target stack).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
  exact currentStackCellIs_atomsBelow stack position _

theorem currentConfigIs_atomsBelow (target : tm.Cfg) :
    (currentConfigIs (tm := tm) (space := space) (clockBits := clockBits)
      target).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  refine ⟨currentLabelIs_atomsBelow target.l,
    currentControlIs_atomsBelow target.var, ?_⟩
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
  exact currentStackIs_atomsBelow target stack

/-- Require every represented cell of one next-slice stack to equal the
corresponding cell of a fixed target configuration. -/
def nextStackIs (target : tm.Cfg) (stack : tm.K) : TransitionExpr :=
  TransitionExpr.all ((List.finRange space).map fun position =>
    nextStackCellIs (tm := tm) (clockBits := clockBits) stack position
      (target.stk stack)[position.val]?)

/-- Require the bounded machine configuration in the next slice to equal a
fixed target configuration. -/
def nextConfigIs (target : tm.Cfg) : TransitionExpr :=
  .and
    (nextLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) target.l)
    (.and
      (nextControlIs (tm := tm) (space := space)
        (clockBits := clockBits) target.var)
      (TransitionExpr.all ((finiteValues tm.K).map fun stack =>
        nextStackIs (tm := tm) (space := space)
          (clockBits := clockBits) target stack)))

/-- Canonical bounded stack encodings satisfy `nextStackIs` exactly when the
semantic next stack equals the target stack. -/
theorem nextStackIs_encode_iff
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (target : tm.Cfg) (stack : tm.K)
    (nextFits : (next.config.stk stack).length ≤ space)
    (targetFits : (target.stk stack).length ≤ space) :
    (nextStackIs (tm := tm) (space := space) (clockBits := clockBits)
      target stack).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      next.config.stk stack = target.stk stack := by
  rw [nextStackIs, TransitionExpr.all_eval, List.all_eq_true]
  constructor
  · intro cells
    apply List.ext_getElem?
    intro index
    by_cases indexInRange : index < space
    · let position : Fin space := ⟨index, indexInRange⟩
      have cell := cells
        (nextStackCellIs (tm := tm) (clockBits := clockBits) stack position
          (target.stk stack)[position.val]?)
        (List.mem_map.mpr ⟨position, by simp, rfl⟩)
      simpa [nextStackCellIs, TransitionExpr.next, TransitionExpr.eval,
        TransitionWire.value, position] using cell
    · have spaceLe : space ≤ index := Nat.not_lt.mp indexInRange
      rw [List.getElem?_eq_none (le_trans nextFits spaceLe),
        List.getElem?_eq_none (le_trans targetFits spaceLe)]
  · intro stacksEq expression expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    simpa [nextStackCellIs, TransitionExpr.next, TransitionExpr.eval,
      TransitionWire.value, stacksEq]

private theorem cfg_eq_of_fields {first second : tm.Cfg}
    (labelEq : first.l = second.l)
    (controlEq : first.var = second.var)
    (stacksEq : ∀ stack, first.stk stack = second.stk stack) :
    first = second := by
  cases first with
  | mk firstLabel firstControl firstStacks =>
    cases second with
    | mk secondLabel secondControl secondStacks =>
      congr 1
      funext stack
      exact stacksEq stack

/-- On canonical bounded encodings, `nextConfigIs target` is precisely
semantic equality with `target`. -/
theorem nextConfigIs_encode_iff
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (target : tm.Cfg)
    (nextFits : ∀ stack, (next.config.stk stack).length ≤ space)
    (targetFits : ∀ stack, (target.stk stack).length ≤ space) :
    (nextConfigIs (tm := tm) (space := space) (clockBits := clockBits)
      target).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      next.config = target := by
  simp only [nextConfigIs, TransitionExpr.eval, Bool.and_eq_true]
  constructor
  · rintro ⟨labelEq, controlEq, stacksTrue⟩
    apply cfg_eq_of_fields
    · simpa [nextLabelIs, TransitionExpr.next, TransitionExpr.eval,
        TransitionWire.value] using labelEq
    · simpa [nextControlIs, TransitionExpr.next, TransitionExpr.eval,
        TransitionWire.value] using controlEq
    · intro stack
      apply (nextStackIs_encode_iff current next target stack
        (nextFits stack) (targetFits stack)).mp
      rw [TransitionExpr.all_eval, List.all_eq_true] at stacksTrue
      exact stacksTrue _
        (List.mem_map.mpr ⟨stack, mem_finiteValues stack, rfl⟩)
  · intro configEq
    subst target
    refine ⟨?_, ?_, ?_⟩
    · simp [nextLabelIs, TransitionExpr.next, TransitionExpr.eval,
        TransitionWire.value]
    · simp [nextControlIs, TransitionExpr.next, TransitionExpr.eval,
        TransitionWire.value]
    · rw [TransitionExpr.all_eval, List.all_eq_true]
      intro expression expressionMem
      obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
      exact (nextStackIs_encode_iff current next next.config stack
        (nextFits stack) (nextFits stack)).mpr rfl

theorem nextStackIs_atomsBelow (target : tm.Cfg) (stack : tm.K) :
    (nextStackIs (tm := tm) (space := space) (clockBits := clockBits)
      target stack).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
  exact nextStackCellIs_atomsBelow stack position _

theorem nextConfigIs_atomsBelow (target : tm.Cfg) :
    (nextConfigIs (tm := tm) (space := space) (clockBits := clockBits)
      target).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  refine ⟨nextLabelIs_atomsBelow target.l,
    nextControlIs_atomsBelow target.var, ?_⟩
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
  exact nextStackIs_atomsBelow target stack

/-- The halted label is the accepting condition for the bundled TM2 machine. -/
def machineAccepts (config : tm.Cfg) : Prop :=
  config.l = none

/-- Boolean expression for the halted-label accepting condition. -/
def machineAcceptsExpression : TransitionExpr :=
  currentLabelIs (tm := tm) (space := space) (clockBits := clockBits) none

/-- Accepting edges reset the clock and return to the fixed initial
configuration. -/
def machineResetExpression (initial : tm.Cfg) : TransitionExpr :=
  .and
    (machineAcceptsExpression (tm := tm) (space := space)
      (clockBits := clockBits))
    (.and
      (clockReset (tm := tm) (space := space) (clockBits := clockBits))
      (nextConfigIs (tm := tm) (space := space)
        (clockBits := clockBits) initial))

/-- Nonaccepting edges execute one ordinary machine step and increment the
fixed-width clock without overflow. -/
def machineOrdinaryExpression : TransitionExpr :=
  .and
    (.not (machineAcceptsExpression (tm := tm) (space := space)
      (clockBits := clockBits)))
    (.and
      (clockSuccessor (tm := tm) (space := space)
        (clockBits := clockBits))
      (machineStepExpression (tm := tm) (space := space)
        (clockBits := clockBits)))

/-- Complete local Boolean relation for a bounded accepting-reset TM2
computation.  Structural constraints apply to the current slice; on a cyclic
history every slice is current on one edge. -/
def machineResetClockExpression (initial : tm.Cfg) : TransitionExpr :=
  .and
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits))
    (.or
      (machineResetExpression (tm := tm) (space := space)
        (clockBits := clockBits) initial)
      (machineOrdinaryExpression (tm := tm) (space := space)
        (clockBits := clockBits)))

theorem machineAcceptsExpression_encode_iff
    (current next : PeriodicComputation.ResetClockState tm.Cfg) :
    (machineAcceptsExpression (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      machineAccepts (tm := tm) current.config := by
  simp [machineAcceptsExpression, currentLabelIs, TransitionExpr.current,
    TransitionExpr.eval, TransitionWire.value, machineAccepts]

private theorem oneHotFields_encode_between
    (current next : PeriodicComputation.ResetClockState tm.Cfg) :
    (oneHotFields (tm := tm) (space := space) (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true := by
  rw [oneHotFields, TransitionExpr.all_eval, List.all_eq_true]
  intro expression expressionMem
  rw [oneHotFieldExpressions, List.mem_append] at expressionMem
  rcases expressionMem with expressionMem | expressionMem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at expressionMem
    rcases expressionMem with rfl | rfl
    · exact (TransitionExpr.currentExactlyOne_eval_iff _ _ _).mpr
        (encoded_label_exactlyOne current)
    · exact (TransitionExpr.currentExactlyOne_eval_iff _ _ _).mpr
        (encoded_state_exactlyOne current)
  · rw [List.mem_flatMap] at expressionMem
    obtain ⟨stack, _, expressionMem⟩ := expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    exact (TransitionExpr.currentExactlyOne_eval_iff _ _ _).mpr
      (encoded_stack_exactlyOne current stack position)

private theorem stackSuffixExpression_encode_between
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (stack : tm.K) (index : Nat) :
    (stackSuffixExpression (space := space) (clockBits := clockBits)
      stack index).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true := by
  unfold stackSuffixExpression
  split
  next nextExists =>
    simp only [TransitionExpr.eval, TransitionExpr.current_eval,
      stackNoneAtom]
    rw [encode_stack, encode_stack]
    by_cases currentNone : (current.config.stk stack)[index]? = none
    · have lengthLe : (current.config.stk stack).length ≤ index :=
        List.getElem?_eq_none_iff.mp currentNone
      have nextNone :
          (current.config.stk stack)[index + 1]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      simp [currentNone, nextNone]
    · simp [currentNone]
  next => rfl

private theorem stackSuffixFields_encode_between
    (current next : PeriodicComputation.ResetClockState tm.Cfg) :
    (stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true := by
  rw [stackSuffixFields, TransitionExpr.all_eval, List.all_eq_true]
  intro expression expressionMem
  rw [allStackSuffixExpressions, List.mem_flatMap] at expressionMem
  obtain ⟨stack, _, expressionMem⟩ := expressionMem
  rw [stackSuffixExpressions] at expressionMem
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackSuffixExpression_encode_between current next stack index

private theorem wellFormedFields_encode_between
    (current next : PeriodicComputation.ResetClockState tm.Cfg) :
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true := by
  simp [wellFormedFields, TransitionExpr.eval,
    oneHotFields_encode_between current next,
    stackSuffixFields_encode_between current next]

/-- Canonical encodings satisfy the complete expression exactly when their
semantic states are related by the accepting-reset clock relation. -/
theorem machineResetClockExpression_encode_iff
    (initial : tm.Cfg)
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space)
    (currentStacksFit :
      ∀ stack, (current.config.stk stack).length ≤ space)
    (nextStacksFit : ∀ stack, (next.config.stk stack).length ≤ space)
    (currentClockFits : current.clock < 2 ^ clockBits)
    (nextClockFits : next.clock < 2 ^ clockBits) :
    (machineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      PeriodicComputation.ResetClockRelation initial tm.step
        (machineAccepts (tm := tm)) (2 ^ clockBits - 1) current next := by
  have acceptsIff := machineAcceptsExpression_encode_iff
    (space := space) (clockBits := clockBits) current next
  have resetIff := clockReset_encode_iff
    (space := space) (clockBits := clockBits) current next nextClockFits
  have initialIff := nextConfigIs_encode_iff
    (space := space) (clockBits := clockBits) current next initial
    nextStacksFit initialStacksFit
  have successorIff := clockSuccessor_encode_iff
    (space := space) (clockBits := clockBits) current next
    currentClockFits nextClockFits
  have stepIff := machineStepExpression_encode_iff
    (space := space) (clockBits := clockBits) current next
    currentStacksFit nextStacksFit
  have wellFormedTrue :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval
          (encode (space := space) (clockBits := clockBits) current)
          (encode (space := space) (clockBits := clockBits) next) = true := by
    exact wellFormedFields_encode_between current next
  rw [machineResetClockExpression, TransitionExpr.eval, Bool.and_eq_true,
    wellFormedTrue]
  simp only [true_and, Bool.or_eq_true]
  rw [machineResetExpression, machineOrdinaryExpression]
  simp only [TransitionExpr.eval]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  rw [acceptsIff, resetIff, initialIff, successorIff, stepIff]
  have notAcceptsIff :
      (machineAcceptsExpression (tm := tm) (space := space)
          (clockBits := clockBits)).eval
          (encode (space := space) (clockBits := clockBits) current)
          (encode (space := space) (clockBits := clockBits) next) = false ↔
        ¬ machineAccepts (tm := tm) current.config := by
    simp [machineAcceptsExpression, currentLabelIs, TransitionExpr.current,
      TransitionExpr.eval, TransitionWire.value, machineAccepts]
  have notAcceptsTrueIff :
      (!((machineAcceptsExpression (tm := tm) (space := space)
          (clockBits := clockBits)).eval
          (encode (space := space) (clockBits := clockBits) current)
          (encode (space := space) (clockBits := clockBits) next))) = true ↔
        ¬ machineAccepts (tm := tm) current.config := by
    rw [Bool.not_eq_true_eq_eq_false, notAcceptsIff]
  rw [notAcceptsTrueIff]
  unfold PeriodicComputation.ResetClockRelation
  constructor
  · intro branch
    have currentBound : current.clock ≤ 2 ^ clockBits - 1 := by omega
    have nextBound : next.clock ≤ 2 ^ clockBits - 1 := by omega
    refine ⟨currentBound, nextBound, ?_⟩
    rcases branch with reset | ordinary
    · left
      refine ⟨reset.1, ?_⟩
      cases current
      cases next
      simp_all
    · right
      refine ⟨ordinary.1, ?_, ordinary.2.1, ordinary.2.2⟩
      omega
  · rintro ⟨_, _, reset | ordinary⟩
    · left
      rcases reset with ⟨accepts, nextEq⟩
      subst next
      exact ⟨accepts, rfl, rfl⟩
    · right
      exact ⟨ordinary.1, ordinary.2.2.1, ordinary.2.2.2⟩

theorem machineResetClockExpression_atomsBelow (initial : tm.Cfg) :
    (machineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  refine ⟨wellFormedFields_atomsBelow,
    ⟨currentLabelIs_atomsBelow none,
      clockReset_atomsBelow, nextConfigIs_atomsBelow initial⟩,
    currentLabelIs_atomsBelow none,
      clockSuccessor_atomsBelow, machineStepExpression_atomsBelow⟩

/-- Acceptance at one designated terminal configuration.  This distinguishes
the `true` output of a decider from its likewise-halted `false` output. -/
def designatedMachineAccepts (accepting config : tm.Cfg) : Prop :=
  config = accepting

def designatedMachineAcceptsExpression (accepting : tm.Cfg) : TransitionExpr :=
  currentConfigIs (tm := tm) (space := space)
    (clockBits := clockBits) accepting

def designatedMachineResetExpression (initial accepting : tm.Cfg) :
    TransitionExpr :=
  .and
    (designatedMachineAcceptsExpression (tm := tm) (space := space)
      (clockBits := clockBits) accepting)
    (.and
      (clockReset (tm := tm) (space := space) (clockBits := clockBits))
      (nextConfigIs (tm := tm) (space := space)
        (clockBits := clockBits) initial))

def designatedMachineOrdinaryExpression (accepting : tm.Cfg) :
    TransitionExpr :=
  .and
    (.not (designatedMachineAcceptsExpression (tm := tm) (space := space)
      (clockBits := clockBits) accepting))
    (.and
      (clockSuccessor (tm := tm) (space := space)
        (clockBits := clockBits))
      (machineStepExpression (tm := tm) (space := space)
        (clockBits := clockBits)))

/-- Complete reset-clock relation whose sole accepting state is a designated
bounded terminal configuration. -/
def designatedMachineResetClockExpression (initial accepting : tm.Cfg) :
    TransitionExpr :=
  .and
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits))
    (.or
      (designatedMachineResetExpression (tm := tm) (space := space)
        (clockBits := clockBits) initial accepting)
      (designatedMachineOrdinaryExpression (tm := tm) (space := space)
        (clockBits := clockBits) accepting))

/-- Canonical bounded encodings realize exactly the designated accepting
reset-clock relation. -/
theorem designatedMachineResetClockExpression_encode_iff
    (initial accepting : tm.Cfg)
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space)
    (acceptingStacksFit : ∀ stack, (accepting.stk stack).length ≤ space)
    (currentStacksFit :
      ∀ stack, (current.config.stk stack).length ≤ space)
    (nextStacksFit : ∀ stack, (next.config.stk stack).length ≤ space)
    (currentClockFits : current.clock < 2 ^ clockBits)
    (nextClockFits : next.clock < 2 ^ clockBits) :
    (designatedMachineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      PeriodicComputation.ResetClockRelation initial tm.step
        (designatedMachineAccepts accepting) (2 ^ clockBits - 1)
        current next := by
  have acceptsIff :
      (designatedMachineAcceptsExpression (tm := tm) (space := space)
        (clockBits := clockBits) accepting).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      designatedMachineAccepts accepting current.config := by
    exact currentConfigIs_encode_iff current next accepting
      currentStacksFit acceptingStacksFit
  have resetIff := clockReset_encode_iff
    (space := space) (clockBits := clockBits) current next nextClockFits
  have initialIff := nextConfigIs_encode_iff
    (space := space) (clockBits := clockBits) current next initial
    nextStacksFit initialStacksFit
  have successorIff := clockSuccessor_encode_iff
    (space := space) (clockBits := clockBits) current next
    currentClockFits nextClockFits
  have stepIff := machineStepExpression_encode_iff
    (space := space) (clockBits := clockBits) current next
    currentStacksFit nextStacksFit
  have wellFormedTrue := wellFormedFields_encode_between
    (space := space) (clockBits := clockBits) current next
  rw [designatedMachineResetClockExpression, TransitionExpr.eval,
    Bool.and_eq_true, wellFormedTrue]
  simp only [true_and, Bool.or_eq_true]
  rw [designatedMachineResetExpression,
    designatedMachineOrdinaryExpression]
  simp only [TransitionExpr.eval, Bool.or_eq_true, Bool.and_eq_true]
  rw [acceptsIff, resetIff, initialIff, successorIff, stepIff]
  have notAcceptsIff :
      (designatedMachineAcceptsExpression (tm := tm) (space := space)
        (clockBits := clockBits) accepting).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = false ↔
      ¬ designatedMachineAccepts accepting current.config := by
    constructor
    · intro expressionFalse accepted
      have expressionTrue := acceptsIff.mpr accepted
      rw [expressionFalse] at expressionTrue
      contradiction
    · intro notAccepted
      cases expressionValue :
          (designatedMachineAcceptsExpression (tm := tm) (space := space)
            (clockBits := clockBits) accepting).eval
          (encode (space := space) (clockBits := clockBits) current)
          (encode (space := space) (clockBits := clockBits) next) with
      | false => rfl
      | true => exact (notAccepted (acceptsIff.mp expressionValue)).elim
  have notAcceptsTrueIff :
      (!(designatedMachineAcceptsExpression (tm := tm) (space := space)
        (clockBits := clockBits) accepting).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next)) = true ↔
      ¬ designatedMachineAccepts accepting current.config := by
    rw [Bool.not_eq_true_eq_eq_false, notAcceptsIff]
  rw [notAcceptsTrueIff]
  unfold PeriodicComputation.ResetClockRelation
  constructor
  · intro branch
    have currentBound : current.clock ≤ 2 ^ clockBits - 1 := by omega
    have nextBound : next.clock ≤ 2 ^ clockBits - 1 := by omega
    refine ⟨currentBound, nextBound, ?_⟩
    rcases branch with reset | ordinary
    · left
      refine ⟨reset.1, ?_⟩
      cases current
      cases next
      simp_all
    · right
      refine ⟨ordinary.1, ?_, ordinary.2.1, ordinary.2.2⟩
      omega
  · rintro ⟨_, _, reset | ordinary⟩
    · left
      rcases reset with ⟨accepts, nextEq⟩
      subst next
      exact ⟨accepts, rfl, rfl⟩
    · right
      exact ⟨ordinary.1, ordinary.2.2.1, ordinary.2.2.2⟩

theorem designatedMachineResetClockExpression_atomsBelow
    (initial accepting : tm.Cfg) :
    (designatedMachineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  refine ⟨wellFormedFields_atomsBelow,
    ⟨currentConfigIs_atomsBelow accepting,
      clockReset_atomsBelow, nextConfigIs_atomsBelow initial⟩,
    currentConfigIs_atomsBelow accepting,
      clockSuccessor_atomsBelow, machineStepExpression_atomsBelow⟩

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
