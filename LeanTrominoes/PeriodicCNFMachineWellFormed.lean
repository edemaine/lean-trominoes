/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineValuation

/-!
# Well-formed bounded machine slices

Exact-one stack cells alone permit a `none` cell followed by a later occupied
cell.  Such a valuation does not encode a list.  This file adds the local
suffix constraint saying that once a bounded stack cell is `none`, every
later cell is also `none`, and proves that canonical list encodings satisfy
it.  Together with the exact-one fields this is the structural
well-formedness predicate for bounded machine slices.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing
open PeriodicComputation

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Atom selecting `none` at one bounded stack position. -/
def stackNoneAtom (stack : tm.K) (position : Fin space) : Nat :=
  code (.stack ⟨stack, position, none⟩ :
    BoundedMachineAtom tm space clockBits)

theorem stackNoneAtom_below (stack : tm.K) (position : Fin space) :
    stackNoneAtom (clockBits := clockBits) stack position <
      atomCount (tm := tm) (space := space) (clockBits := clockBits) :=
  code_lt_atomCount _

/-- If both positions exist, `none` at `index` implies `none` at
`index + 1`.  The final list index emits a harmless true expression. -/
def stackSuffixExpression (stack : tm.K) (index : Nat) : TransitionExpr :=
  if nextExists : index + 1 < space then
    .or
      (.not (.current (stackNoneAtom (clockBits := clockBits) stack
        ⟨index, Nat.lt_of_succ_lt nextExists⟩)))
      (.current (stackNoneAtom (clockBits := clockBits) stack
        ⟨index + 1, nextExists⟩))
  else
    .constant true

theorem stackSuffixExpression_encode (state : ResetClockState tm.Cfg)
    (stack : tm.K) (index : Nat) :
    (stackSuffixExpression (space := space) (clockBits := clockBits)
      stack index).eval
        (encode (space := space) (clockBits := clockBits) state)
        (encode (space := space) (clockBits := clockBits) state) = true := by
  unfold stackSuffixExpression
  split
  next nextExists =>
    simp only [TransitionExpr.eval, TransitionExpr.current_eval,
      stackNoneAtom]
    rw [encode_stack, encode_stack]
    by_cases currentNone : (state.config.stk stack)[index]? = none
    · have lengthLe : (state.config.stk stack).length ≤ index :=
        List.getElem?_eq_none_iff.mp currentNone
      have nextNone :
          (state.config.stk stack)[index + 1]? = none :=
        List.getElem?_eq_none_iff.mpr (by omega)
      simp [currentNone, nextNone]
    · simp [currentNone]
  next => rfl

theorem stackSuffixExpression_atomsBelow (stack : tm.K) (index : Nat) :
    (stackSuffixExpression (space := space) (clockBits := clockBits)
      stack index).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  unfold stackSuffixExpression
  split
  next nextExists =>
    exact ⟨stackNoneAtom_below stack ⟨index, by omega⟩,
      stackNoneAtom_below stack ⟨index + 1, nextExists⟩⟩
  next => trivial

/-- All adjacent suffix constraints for one bounded stack. -/
def stackSuffixExpressions (stack : tm.K) : List TransitionExpr :=
  (List.range space).map
    (stackSuffixExpression (space := space) (clockBits := clockBits) stack)

/-- Adjacent suffix constraints for every stack. -/
def allStackSuffixExpressions : List TransitionExpr :=
  (finiteValues tm.K).flatMap
    (stackSuffixExpressions (space := space) (clockBits := clockBits))

/-- The conjunction asserting that every bounded stack is a `some` prefix
followed by a `none` suffix. -/
def stackSuffixFields : TransitionExpr :=
  TransitionExpr.all
    (allStackSuffixExpressions (tm := tm) (space := space)
      (clockBits := clockBits))

theorem stackSuffixFields_encode (state : ResetClockState tm.Cfg) :
    (stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) state)
        (encode (space := space) (clockBits := clockBits) state) = true := by
  rw [stackSuffixFields, TransitionExpr.all_eval, List.all_eq_true]
  intro expression expressionMem
  rw [allStackSuffixExpressions, List.mem_flatMap] at expressionMem
  obtain ⟨stack, _, expressionMem⟩ := expressionMem
  rw [stackSuffixExpressions] at expressionMem
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackSuffixExpression_encode state stack index

theorem stackSuffixFields_atomsBelow :
    (stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  rw [allStackSuffixExpressions, List.mem_flatMap] at expressionMem
  obtain ⟨stack, _, expressionMem⟩ := expressionMem
  rw [stackSuffixExpressions] at expressionMem
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackSuffixExpression_atomsBelow stack index

/-- Complete structural well-formedness constraint for one bounded slice. -/
def wellFormedFields : TransitionExpr :=
  .and
    (oneHotFields (tm := tm) (space := space) (clockBits := clockBits))
    (stackSuffixFields (tm := tm) (space := space) (clockBits := clockBits))

theorem wellFormedFields_encode (state : ResetClockState tm.Cfg) :
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) state)
        (encode (space := space) (clockBits := clockBits) state) = true := by
  simp [wellFormedFields, TransitionExpr.eval,
    oneHotFields_encode, stackSuffixFields_encode]

theorem wellFormedFields_atomsBelow :
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
  ⟨oneHotFields_atomsBelow, stackSuffixFields_atomsBelow⟩

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
