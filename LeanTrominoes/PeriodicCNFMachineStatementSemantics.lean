/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStatementPaths

/-!
# Semantics of finite TM2 statement paths

This file connects each generated terminal statement path to one ordinary TM2
configuration.  It then proves, by induction over `Stmt`, that the disjunction
of all generated paths is exactly Mathlib's atomic `TM2.stepAux` semantics.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Apply a dependent family of normalized transforms to ordinary stacks. -/
def applyStackTransforms
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (stackContents : ∀ stack, List (tm.Γ stack)) :
    ∀ stack, List (tm.Γ stack) :=
  fun stack => (transforms stack).apply (stackContents stack)

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

/-- Ordinary TM2 configuration described by a terminal symbolic path. -/
def StatementPath.outputCfg
    (path : StatementPath tm space clockBits) (current : tm.Cfg) : tm.Cfg where
  l := path.label
  var := path.control
  stk := applyStackTransforms path.transforms current.stk

/-- Semantic interpretation of one guarded terminal path. -/
def StatementPath.Realizes
    (path : StatementPath tm space clockBits)
    (currentValues nextValues : Nat → Bool) : Prop :=
  path.guard.eval currentValues nextValues = true ∧
    (decode (tm := tm) (space := space)
      (clockBits := clockBits) nextValues).toCfg =
      path.outputCfg ((decode (tm := tm) (space := space)
        (clockBits := clockBits) currentValues).toCfg)

theorem StatementPath.stackExpression_eval_iff
    {currentValues nextValues : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval nextValues nextValues = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (nextShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) nextValues).StackShaped)
    (path : StatementPath tm space clockBits) :
    path.stackExpression.eval currentValues nextValues = true ↔
      ∀ stack,
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) nextValues).toCfg.stk stack =
        (path.transforms stack).apply
          ((decode (tm := tm) (space := space)
            (clockBits := clockBits) currentValues).toCfg.stk stack) := by
  rw [StatementPath.stackExpression, TransitionExpr.all_eval,
    List.all_eq_true]
  constructor
  · intro expressionsTrue stack
    apply (stackTransformExpression_eval_iff_toCfg
      currentOneHot nextOneHot currentShaped nextShaped stack
      (path.transforms stack)).mp
    apply expressionsTrue
    exact List.mem_map.mpr ⟨stack, mem_finiteValues stack, rfl⟩
  · intro stacksEqual expression expressionMem
    obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
    exact (stackTransformExpression_eval_iff_toCfg
      currentOneHot nextOneHot currentShaped nextShaped stack
      (path.transforms stack)).mpr (stacksEqual stack)

/-- A terminal path expression has exactly its guarded configuration
semantics on arbitrary structurally well-formed slices. -/
theorem StatementPath.expression_eval_iff
    {currentValues nextValues : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval nextValues nextValues = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (nextShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) nextValues).StackShaped)
    (path : StatementPath tm space clockBits) :
    path.expression.eval currentValues nextValues = true ↔
      path.Realizes currentValues nextValues := by
  let currentCfg := (decode (tm := tm) (space := space)
    (clockBits := clockBits) currentValues).toCfg
  let nextCfg := (decode (tm := tm) (space := space)
    (clockBits := clockBits) nextValues).toCfg
  rw [StatementPath.expression, TransitionExpr.all_eval,
    List.all_eq_true]
  constructor
  · intro expressionsTrue
    have guardTrue := expressionsTrue path.guard (by simp)
    have labelTrue := expressionsTrue
      (nextLabelIs (tm := tm) (space := space)
        (clockBits := clockBits) path.label) (by simp)
    have controlTrue := expressionsTrue
      (nextControlIs (tm := tm) (space := space)
        (clockBits := clockBits) path.control) (by simp)
    have stacksTrue := expressionsTrue path.stackExpression (by simp)
    have labelEq : nextCfg.l = path.label := by
      rw [nextLabelIs_eval_decode nextOneHot] at labelTrue
      simpa [nextCfg] using labelTrue
    have controlEq : nextCfg.var = path.control := by
      rw [nextControlIs_eval_decode nextOneHot] at controlTrue
      simpa [nextCfg] using controlTrue
    have stacksEq : ∀ stack,
        nextCfg.stk stack = (path.transforms stack).apply
          (currentCfg.stk stack) := by
      simpa [currentCfg, nextCfg] using
        (path.stackExpression_eval_iff currentOneHot nextOneHot
          currentShaped nextShaped).mp stacksTrue
    refine ⟨guardTrue, ?_⟩
    apply cfg_eq_of_fields labelEq controlEq
    exact stacksEq
  · rintro ⟨guardTrue, outputEq⟩
    intro expression expressionMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at expressionMem
    rcases expressionMem with rfl | rfl | rfl | rfl
    · exact guardTrue
    · have := congrArg Turing.TM2.Cfg.l outputEq
      rw [nextLabelIs_eval_decode nextOneHot]
      simpa [StatementPath.outputCfg] using this
    · have := congrArg Turing.TM2.Cfg.var outputEq
      rw [nextControlIs_eval_decode nextOneHot]
      simpa [StatementPath.outputCfg] using this
    · apply (path.stackExpression_eval_iff currentOneHot nextOneHot
        currentShaped nextShaped).mpr
      intro stack
      have := congrFun (congrArg Turing.TM2.Cfg.stk outputEq) stack
      simpa [StatementPath.outputCfg, applyStackTransforms] using this

/-- The path disjunction is true exactly when one generated terminal path is
realized. -/
theorem statementPathsExpression_eval_iff_exists
    {currentValues nextValues : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval nextValues nextValues = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (nextShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) nextValues).StackShaped)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (statementPathsExpression (tm := tm) (space := space)
      (clockBits := clockBits) statement control transforms).eval
        currentValues nextValues = true ↔
      ∃ path ∈ statementPaths (space := space) (clockBits := clockBits)
          statement control transforms,
        path.Realizes currentValues nextValues := by
  rw [statementPathsExpression, TransitionExpr.any_eval, List.any_eq_true]
  constructor
  · rintro ⟨expression, expressionMem, expressionTrue⟩
    obtain ⟨path, pathMem, rfl⟩ := List.mem_map.mp expressionMem
    exact ⟨path, pathMem,
      (path.expression_eval_iff currentOneHot nextOneHot
        currentShaped nextShaped).mp expressionTrue⟩
  · rintro ⟨path, pathMem, realizes⟩
    refine ⟨path.expression, List.mem_map.mpr ⟨path, pathMem, rfl⟩, ?_⟩
    exact (path.expression_eval_iff currentOneHot nextOneHot
      currentShaped nextShaped).mpr realizes

private theorem head?_drop_eq_getElem? {Symbol : Type*}
    (symbols : List Symbol) (discard : Nat) :
    (symbols.drop discard).head? = symbols[discard]? := by
  induction discard generalizing symbols with
  | zero => cases symbols <;> rfl
  | succ discard ih =>
      cases symbols with
      | nil => simp
      | cons symbol symbols => exact ih symbols

theorem applyStackTransforms_update_push
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (stackContents : ∀ stack, List (tm.Γ stack))
    (stack : tm.K) (symbol : tm.Γ stack) :
    applyStackTransforms
        (Function.update transforms stack ((transforms stack).push symbol))
        stackContents =
      Function.update (applyStackTransforms transforms stackContents) stack
        (symbol :: applyStackTransforms transforms stackContents stack) := by
  funext other
  by_cases equality : other = stack
  · subst other
    simp [applyStackTransforms]
  · simp [applyStackTransforms, equality]

theorem applyStackTransforms_update_pop
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (stackContents : ∀ stack, List (tm.Γ stack))
    (stack : tm.K) :
    applyStackTransforms
        (Function.update transforms stack (transforms stack).pop)
        stackContents =
      Function.update (applyStackTransforms transforms stackContents) stack
        (applyStackTransforms transforms stackContents stack).tail := by
  funext other
  by_cases equality : other = stack
  · subst other
    simp [applyStackTransforms]
  · simp [applyStackTransforms, equality]

theorem applyStackTransform_head?_of_added_nil
    {currentValues : Nat → Bool}
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (addedNil : transform.added = []) :
    ((transform.apply ((decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).toCfg.stk stack)).head? =
      (if sourceExists : transform.discard < space then
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) currentValues).stack stack
            ⟨transform.discard, sourceExists⟩
      else
        none)) := by
  let slice := decode (tm := tm) (space := space)
    (clockBits := clockBits) currentValues
  rw [StackTransform.apply, addedNil, List.nil_append,
    head?_drop_eq_getElem?]
  by_cases sourceExists : transform.discard < space
  · rw [dif_pos sourceExists]
    exact slice.toCfg_stack_getElem?_eq currentShaped stack
      ⟨transform.discard, sourceExists⟩
  · rw [dif_neg sourceExists]
    apply List.getElem?_eq_none
    exact le_trans (slice.toCfg_stack_length_le stack)
      (Nat.not_lt.mp sourceExists)

@[simp]
theorem StatementPath.andGuard_realizes_iff
    (condition : TransitionExpr) (path : StatementPath tm space clockBits)
    (currentValues nextValues : Nat → Bool) :
    (path.andGuard condition).Realizes currentValues nextValues ↔
      condition.eval currentValues nextValues = true ∧
        path.Realizes currentValues nextValues := by
  simp only [StatementPath.Realizes, StatementPath.andGuard,
    TransitionExpr.eval, Bool.and_eq_true]
  exact and_assoc

/-- Generated paths implement exactly the atomic `TM2.stepAux` result, even
when entered after an accumulated family of normalized stack transforms. -/
theorem statementPaths_realizes_iff_stepAux
    {currentValues nextValues : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues currentValues = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (∃ path ∈ statementPaths (space := space) (clockBits := clockBits)
        statement control transforms,
      path.Realizes currentValues nextValues) ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) nextValues).toCfg =
      Turing.TM2.stepAux statement control
        (applyStackTransforms transforms
          (decode (tm := tm) (space := space)
            (clockBits := clockBits) currentValues).toCfg.stk) := by
  induction statement generalizing control transforms with
  | push stack write next ih =>
      rw [statementPaths, ih]
      simp only [Turing.TM2.stepAux]
      rw [applyStackTransforms_update_push]
  | peek stack read next ih =>
      rw [statementPaths]
      split <;> rename_i addedEq
      · rename_i symbol remaining
        rw [ih]
        simp only [Turing.TM2.stepAux, applyStackTransforms]
        have headEq :
            ((transforms stack).apply
              ((decode (tm := tm) (space := space)
                (clockBits := clockBits) currentValues).toCfg.stk stack)).head? =
              some symbol := by
          simp [StackTransform.apply, addedEq]
        have appliedHeadEq :
            (applyStackTransforms transforms
              (decode (tm := tm) (space := space)
                (clockBits := clockBits) currentValues).toCfg.stk stack).head? =
              some symbol := by
          simpa [applyStackTransforms] using headEq
        rw [headEq]
      · split <;> rename_i sourceExists
        · constructor
          · rintro ⟨guardedPath, guardedMem, guardedRealizes⟩
            rw [List.mem_flatMap] at guardedMem
            obtain ⟨observed, _, guardedMem⟩ := guardedMem
            obtain ⟨path, pathMem, pathEq⟩ := List.mem_map.mp guardedMem
            subst guardedPath
            obtain ⟨observedTrue, pathRealizes⟩ :=
              (path.andGuard_realizes_iff _ _ _).mp guardedRealizes
            rw [currentStackCellIs_eval_decode currentOneHot] at observedTrue
            have observedEq :
                (decode (tm := tm) (space := space)
                  (clockBits := clockBits) currentValues).stack stack
                    ⟨(transforms stack).discard, sourceExists⟩ = observed := by
              simpa using observedTrue
            have recursive := (ih (read control observed) transforms).mp
              ⟨path, pathMem, pathRealizes⟩
            simp only [Turing.TM2.stepAux]
            have headEq := applyStackTransform_head?_of_added_nil
              currentShaped stack (transforms stack) addedEq
            rw [dif_pos sourceExists, observedEq] at headEq
            have appliedHeadEq :
                (applyStackTransforms transforms
                  (decode (tm := tm) (space := space)
                    (clockBits := clockBits) currentValues).toCfg.stk
                    stack).head? = observed := by
              simpa [applyStackTransforms] using headEq
            rw [appliedHeadEq]
            exact recursive
          · intro stepEq
            let observed := (decode (tm := tm) (space := space)
              (clockBits := clockBits) currentValues).stack stack
                ⟨(transforms stack).discard, sourceExists⟩
            have headEq := applyStackTransform_head?_of_added_nil
              currentShaped stack (transforms stack) addedEq
            rw [dif_pos sourceExists] at headEq
            have appliedHeadEq :
                (applyStackTransforms transforms
                  (decode (tm := tm) (space := space)
                    (clockBits := clockBits) currentValues).toCfg.stk
                    stack).head? = observed := by
              simpa [applyStackTransforms, observed] using headEq
            simp only [Turing.TM2.stepAux] at stepEq
            rw [appliedHeadEq] at stepEq
            have recursive :
                (decode (tm := tm) (space := space)
                  (clockBits := clockBits) nextValues).toCfg =
                Turing.TM2.stepAux next (read control observed)
                  (applyStackTransforms transforms
                    (decode (tm := tm) (space := space)
                      (clockBits := clockBits) currentValues).toCfg.stk) := by
              exact stepEq
            obtain ⟨path, pathMem, pathRealizes⟩ :=
              (ih (read control observed) transforms).mpr recursive
            refine ⟨path.andGuard
              (currentStackCellIs (tm := tm) (clockBits := clockBits) stack
                ⟨(transforms stack).discard, sourceExists⟩ observed), ?_, ?_⟩
            · rw [List.mem_flatMap]
              refine ⟨observed, mem_finiteValues observed, ?_⟩
              exact List.mem_map.mpr ⟨path, pathMem, rfl⟩
            · apply (path.andGuard_realizes_iff _ _ _).mpr
              refine ⟨?_, pathRealizes⟩
              rw [currentStackCellIs_eval_decode currentOneHot]
              simp [observed]
        · rw [ih]
          simp only [Turing.TM2.stepAux]
          have headEq := applyStackTransform_head?_of_added_nil
            currentShaped stack (transforms stack) addedEq
          rw [dif_neg sourceExists] at headEq
          have appliedHeadEq :
              (applyStackTransforms transforms
                (decode (tm := tm) (space := space)
                  (clockBits := clockBits) currentValues).toCfg.stk stack).head? =
                none := by
            simpa [applyStackTransforms] using headEq
          rw [appliedHeadEq]
  | pop stack read next ih =>
      let popped := Function.update transforms stack (transforms stack).pop
      rw [statementPaths]
      split <;> rename_i addedEq
      · rename_i symbol remaining
        rw [ih]
        simp only [Turing.TM2.stepAux, applyStackTransforms]
        have headEq :
            ((transforms stack).apply
              ((decode (tm := tm) (space := space)
                (clockBits := clockBits) currentValues).toCfg.stk stack)).head? =
              some symbol := by
          simp [StackTransform.apply, addedEq]
        have appliedHeadEq :
            (applyStackTransforms transforms
              (decode (tm := tm) (space := space)
                (clockBits := clockBits) currentValues).toCfg.stk stack).head? =
              some symbol := by
          simpa [applyStackTransforms] using headEq
        have appliedStackEq :
            applyStackTransforms transforms
                (decode (tm := tm) (space := space)
                  (clockBits := clockBits) currentValues).toCfg.stk stack =
              (transforms stack).apply
                ((decode (tm := tm) (space := space)
                  (clockBits := clockBits) currentValues).toCfg.stk stack) :=
          rfl
        rw [applyStackTransforms_update_pop, headEq, appliedStackEq]
      · split <;> rename_i sourceExists
        · constructor
          · rintro ⟨guardedPath, guardedMem, guardedRealizes⟩
            rw [List.mem_flatMap] at guardedMem
            obtain ⟨observed, _, guardedMem⟩ := guardedMem
            obtain ⟨path, pathMem, pathEq⟩ := List.mem_map.mp guardedMem
            subst guardedPath
            obtain ⟨observedTrue, pathRealizes⟩ :=
              (path.andGuard_realizes_iff _ _ _).mp guardedRealizes
            rw [currentStackCellIs_eval_decode currentOneHot] at observedTrue
            have observedEq :
                (decode (tm := tm) (space := space)
                  (clockBits := clockBits) currentValues).stack stack
                    ⟨(transforms stack).discard, sourceExists⟩ = observed := by
              simpa using observedTrue
            have recursive := (ih (read control observed) popped).mp
              ⟨path, pathMem, pathRealizes⟩
            simp only [Turing.TM2.stepAux]
            have headEq := applyStackTransform_head?_of_added_nil
              currentShaped stack (transforms stack) addedEq
            rw [dif_pos sourceExists, observedEq] at headEq
            have appliedHeadEq :
                (applyStackTransforms transforms
                  (decode (tm := tm) (space := space)
                    (clockBits := clockBits) currentValues).toCfg.stk
                    stack).head? = observed := by
              simpa [applyStackTransforms] using headEq
            rw [applyStackTransforms_update_pop] at recursive
            rw [appliedHeadEq]
            exact recursive
          · intro stepEq
            let observed := (decode (tm := tm) (space := space)
              (clockBits := clockBits) currentValues).stack stack
                ⟨(transforms stack).discard, sourceExists⟩
            have headEq := applyStackTransform_head?_of_added_nil
              currentShaped stack (transforms stack) addedEq
            rw [dif_pos sourceExists] at headEq
            have appliedHeadEq :
                (applyStackTransforms transforms
                  (decode (tm := tm) (space := space)
                    (clockBits := clockBits) currentValues).toCfg.stk
                    stack).head? = observed := by
              simpa [applyStackTransforms, observed] using headEq
            simp only [Turing.TM2.stepAux] at stepEq
            rw [appliedHeadEq] at stepEq
            have recursive :
                (decode (tm := tm) (space := space)
                  (clockBits := clockBits) nextValues).toCfg =
                Turing.TM2.stepAux next (read control observed)
                  (applyStackTransforms popped
                    (decode (tm := tm) (space := space)
                      (clockBits := clockBits) currentValues).toCfg.stk) := by
              rw [applyStackTransforms_update_pop]
              exact stepEq
            obtain ⟨path, pathMem, pathRealizes⟩ :=
              (ih (read control observed) popped).mpr recursive
            refine ⟨path.andGuard
              (currentStackCellIs (tm := tm) (clockBits := clockBits) stack
                ⟨(transforms stack).discard, sourceExists⟩ observed), ?_, ?_⟩
            · rw [List.mem_flatMap]
              refine ⟨observed, mem_finiteValues observed, ?_⟩
              exact List.mem_map.mpr ⟨path, pathMem, rfl⟩
            · apply (path.andGuard_realizes_iff _ _ _).mpr
              refine ⟨?_, pathRealizes⟩
              rw [currentStackCellIs_eval_decode currentOneHot]
              simp [observed]
        · rw [ih]
          simp only [Turing.TM2.stepAux]
          have headEq := applyStackTransform_head?_of_added_nil
            currentShaped stack (transforms stack) addedEq
          rw [dif_neg sourceExists] at headEq
          have appliedHeadEq :
              (applyStackTransforms transforms
                (decode (tm := tm) (space := space)
                  (clockBits := clockBits) currentValues).toCfg.stk stack).head? =
                none := by
            simpa [applyStackTransforms] using headEq
          rw [applyStackTransforms_update_pop, appliedHeadEq]
  | load update next ih =>
      rw [statementPaths, ih]
      rfl
  | branch test yes no yesIH noIH =>
      rw [statementPaths]
      cases tested : test control <;> simp only [tested, Bool.false_eq_true,
        ↓reduceIte, Turing.TM2.stepAux]
      · exact noIH control transforms
      · exact yesIH control transforms
  | goto target =>
      simp [statementPaths, StatementPath.Realizes, StatementPath.outputCfg,
        Turing.TM2.stepAux, TransitionExpr.eval]
  | halt =>
      simp [statementPaths, StatementPath.Realizes, StatementPath.outputCfg,
        Turing.TM2.stepAux, TransitionExpr.eval]

theorem applyStackTransforms_identity
    (stackContents : ∀ stack, List (tm.Γ stack)) :
    applyStackTransforms
      (identityStackTransforms (tm := tm)) stackContents = stackContents := by
  funext stack
  simp [applyStackTransforms, identityStackTransforms]

/-- The expression for paths from a fixed current control is exactly one
atomic statement execution from that control. -/
theorem statementPathsExpression_eval_iff_stepAux
    {currentValues nextValues : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval nextValues nextValues = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (nextShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) nextValues).StackShaped)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ) :
    (statementPathsExpression (tm := tm) (space := space)
      (clockBits := clockBits) statement control identityStackTransforms).eval
        currentValues nextValues = true ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) nextValues).toCfg =
      Turing.TM2.stepAux statement control
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) currentValues).toCfg.stk := by
  rw [statementPathsExpression_eval_iff_exists currentOneHot nextOneHot
    currentShaped nextShaped,
    statementPaths_realizes_iff_stepAux currentOneHot currentShaped]
  rw [applyStackTransforms_identity]

/-- Selecting the finite current control turns the statement expression into
the ordinary `stepAux` semantics of the decoded current configuration. -/
theorem statementExpression_eval_iff_stepAux
    {currentValues nextValues : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval nextValues nextValues = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (nextShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) nextValues).StackShaped)
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (statementExpression (tm := tm) (space := space)
      (clockBits := clockBits) statement).eval currentValues nextValues = true ↔
      (decode (tm := tm) (space := space)
        (clockBits := clockBits) nextValues).toCfg =
      Turing.TM2.stepAux statement
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) currentValues).control
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) currentValues).toCfg.stk := by
  rw [statementExpression, TransitionExpr.any_eval, List.any_eq_true]
  constructor
  · rintro ⟨expression, expressionMem, expressionTrue⟩
    obtain ⟨control, _, rfl⟩ := List.mem_map.mp expressionMem
    simp only [TransitionExpr.eval, Bool.and_eq_true] at expressionTrue
    have controlEq :
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) currentValues).control = control := by
      rw [currentControlIs_eval_decode currentOneHot] at expressionTrue
      simpa using expressionTrue.1
    have stepEq := (statementPathsExpression_eval_iff_stepAux
      currentOneHot nextOneHot currentShaped nextShaped statement control).mp
      expressionTrue.2
    rwa [controlEq]
  · intro stepEq
    let control := (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).control
    refine ⟨.and
        (currentControlIs (tm := tm) (space := space)
          (clockBits := clockBits) control)
        (statementPathsExpression (tm := tm) (space := space)
          (clockBits := clockBits) statement control identityStackTransforms),
      List.mem_map.mpr ⟨control, mem_finiteValues control, rfl⟩, ?_⟩
    rw [TransitionExpr.eval, Bool.and_eq_true,
      currentControlIs_eval_decode currentOneHot]
    refine ⟨by simp [control], ?_⟩
    exact (statementPathsExpression_eval_iff_stepAux
      currentOneHot nextOneHot currentShaped nextShaped statement control).mpr
      (by simpa [control] using stepEq)

/-- The complete ordinary-step expression is equivalent to Mathlib's bundled
finite TM2 step function on decoded well-formed slices. -/
theorem BoundedMachineSlice.step_toCfg
    (slice : BoundedMachineSlice tm space clockBits) :
    tm.step slice.toCfg =
      match slice.label with
      | none => none
      | some label =>
          some (Turing.TM2.stepAux (tm.m label) slice.control slice.toCfg.stk) := by
  cases slice with
  | mk label control stack clock =>
      cases label <;> rfl

theorem machineStepExpression_eval_iff_step
    {currentValues nextValues : Nat → Bool}
    (currentOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextOneHot : (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval nextValues nextValues = true)
    (currentShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) currentValues).StackShaped)
    (nextShaped : (decode (tm := tm) (space := space)
      (clockBits := clockBits) nextValues).StackShaped) :
    (machineStepExpression (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues nextValues = true ↔
      tm.step ((decode (tm := tm) (space := space)
        (clockBits := clockBits) currentValues).toCfg) =
        some ((decode (tm := tm) (space := space)
          (clockBits := clockBits) nextValues).toCfg) := by
  rw [machineStepExpression, TransitionExpr.any_eval, List.any_eq_true]
  constructor
  · rintro ⟨expression, expressionMem, expressionTrue⟩
    obtain ⟨label, _, rfl⟩ := List.mem_map.mp expressionMem
    simp only [TransitionExpr.eval, Bool.and_eq_true] at expressionTrue
    have labelEq :
        (decode (tm := tm) (space := space)
          (clockBits := clockBits) currentValues).label = some label := by
      rw [currentLabelIs_eval_decode currentOneHot] at expressionTrue
      simpa using expressionTrue.1
    have resultEq := (statementExpression_eval_iff_stepAux
      currentOneHot nextOneHot currentShaped nextShaped (tm.m label)).mp
      expressionTrue.2
    rw [BoundedMachineSlice.step_toCfg, labelEq]
    exact congrArg some resultEq.symm
  · intro stepEq
    cases labelEq : (decode (tm := tm) (space := space)
        (clockBits := clockBits) currentValues).label with
    | none =>
        rw [BoundedMachineSlice.step_toCfg, labelEq] at stepEq
        simp at stepEq
    | some label =>
        refine ⟨.and
            (currentLabelIs (tm := tm) (space := space)
              (clockBits := clockBits) (some label))
            (statementExpression (tm := tm) (space := space)
              (clockBits := clockBits) (tm.m label)),
          List.mem_map.mpr ⟨label, mem_finiteValues label, rfl⟩, ?_⟩
        rw [TransitionExpr.eval, Bool.and_eq_true,
          currentLabelIs_eval_decode currentOneHot]
        refine ⟨by simp [labelEq], ?_⟩
        apply (statementExpression_eval_iff_stepAux currentOneHot nextOneHot
          currentShaped nextShaped (tm.m label)).mpr
        rw [BoundedMachineSlice.step_toCfg, labelEq] at stepEq
        exact (Option.some.inj stepEq).symm

/-- On canonical bounded encodings, the complete ordinary-step expression is
exactly one step of the bundled TM2 machine. -/
theorem machineStepExpression_encode_iff
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (currentStacksFit :
      ∀ stack, (current.config.stk stack).length ≤ space)
    (nextStacksFit : ∀ stack, (next.config.stk stack).length ≤ space) :
    (machineStepExpression (tm := tm) (space := space)
      (clockBits := clockBits)).eval
        (encode (space := space) (clockBits := clockBits) current)
        (encode (space := space) (clockBits := clockBits) next) = true ↔
      tm.step current.config = some next.config := by
  have currentShaped := decode_stackShaped
    (oneHotFields_encode (space := space) (clockBits := clockBits) current)
    (stackSuffixFields_encode (space := space) (clockBits := clockBits) current)
  have nextShaped := decode_stackShaped
    (oneHotFields_encode (space := space) (clockBits := clockBits) next)
    (stackSuffixFields_encode (space := space) (clockBits := clockBits) next)
  rw [machineStepExpression_eval_iff_step
      (oneHotFields_encode (space := space) (clockBits := clockBits) current)
      (oneHotFields_encode (space := space) (clockBits := clockBits) next)
      currentShaped nextShaped,
    toCfg_decode_encode current currentStacksFit,
    toCfg_decode_encode next nextStacksFit]

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
