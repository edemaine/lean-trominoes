import LeanTrominoes.SpaceRefinement

/-!
# Space refinement for Mathlib's partial-recursive evaluator

Mathlib proves that each sequential evaluator step is simulated by one or
more steps of its four-stack `TM2`, but its refinement theorem intentionally
forgets intermediate configurations.  This module strengthens the individual
simulation routines with `EvalsToInSpace` certificates.
-/

namespace Turing
namespace PartrecToTM2

open StateTransition

private theorem stackSpace_fields (label : Option Λ') (state : Option Γ')
    (tapeStacks : K' → List Γ') :
    TM2.stackSpace (TM2.Cfg.mk label state tapeStacks) =
      (tapeStacks .main).length + (tapeStacks .rev).length +
        (tapeStacks .aux).length + (tapeStacks .stack).length := by
  unfold TM2.stackSpace
  rw [show (Finset.univ : Finset K') =
      {.main, .rev, .aux, .stack} by
    ext stackIndex
    cases stackIndex <;> simp]
  simp [Nat.add_assoc]

private theorem stackSpace_transfer_eq
    (source target : K') (different : source ≠ target)
    (symbol : Γ') (sourceTail : List Γ') (tapeStacks : K' → List Γ')
    (sourceValue : tapeStacks source = symbol :: sourceTail)
    (label : Option Λ') (state : Option Γ') :
    TM2.stackSpace
        ⟨label, state,
          Function.update
            (Function.update tapeStacks source sourceTail)
            target (symbol :: tapeStacks target)⟩ =
      TM2.stackSpace ⟨label, state, tapeStacks⟩ := by
  rw [stackSpace_fields, stackSpace_fields]
  cases source <;> cases target <;>
    simp_all [Function.update] <;> omega

private theorem stackSpace_update_le
    (target : K') (value : List Γ') (tapeStacks : K' → List Γ')
    (lengthBound : value.length ≤ (tapeStacks target).length)
    (label : Option Λ') (state : Option Γ') :
    TM2.stackSpace
        ⟨label, state, Function.update tapeStacks target value⟩ ≤
      TM2.stackSpace ⟨label, state, tapeStacks⟩ := by
  rw [stackSpace_fields, stackSpace_fields]
  cases target <;> simp_all [Function.update]

/-- Moving a prefix from one stack to another never increases total stack
space, including every loop iteration and its final delimiter pop. -/
def move_ok_inSpace {p k₁ k₂ q s L₁ o L₂}
    {tapeStacks : K' → List Γ'} (different : k₁ ≠ k₂)
    (split :
      splitAtPred p (tapeStacks k₁) = (L₁, o, L₂)) :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      (TM2.stackSpace
        ⟨some (Λ'.move p k₁ k₂ q), s, tapeStacks⟩)
      ⟨some (Λ'.move p k₁ k₂ q), s, tapeStacks⟩
      ⟨some q, o,
        Function.update (Function.update tapeStacks k₁ L₂) k₂
          (L₁.reverseAux (tapeStacks k₂))⟩ := by
  induction L₁ generalizing tapeStacks s with
  | nil =>
      have targetUnchanged :
          Function.update
              (Function.update tapeStacks k₁ L₂) k₂
              ([].reverseAux (tapeStacks k₂)) =
            Function.update tapeStacks k₁ L₂ := by
        simp [Function.update_of_ne different.symm]
      have stepEq :
          TM2.step tr
              ⟨some (Λ'.move p k₁ k₂ q), s, tapeStacks⟩ =
            some
              ⟨some q, o,
                Function.update
                  (Function.update tapeStacks k₁ L₂) k₂
                  ([].reverseAux (tapeStacks k₂))⟩ := by
        rw [targetUnchanged]
        revert split
        cases sourceValue : tapeStacks k₁ with
        | nil =>
            intro split
            simp only [splitAtPred] at split
            cases split
            simp [TM2.step, tr.eq_def, pop', sourceValue]
        | cons symbol sourceTail =>
            intro split
            simp only [splitAtPred] at split
            cases predicateValue : p symbol <;>
              simp only [predicateValue, cond_false, cond_true,
                Prod.mk.injEq, true_and, false_and,
                reduceCtorEq] at split
            rcases split with ⟨rfl, rfl⟩
            simp [TM2.step, tr.eq_def, pop', sourceValue,
              predicateValue]
      apply EvalsToInSpace.single stepEq
      · exact Nat.le_refl _
      · rw [targetUnchanged]
        apply stackSpace_update_le
        revert split
        cases sourceValue : tapeStacks k₁ with
        | nil =>
            intro split
            simp only [splitAtPred] at split
            cases split
            simp
        | cons symbol sourceTail =>
            intro split
            simp only [splitAtPred] at split
            cases predicateValue : p symbol <;>
              simp only [predicateValue, cond_false, cond_true,
                Prod.mk.injEq, true_and, false_and,
                reduceCtorEq] at split
            rcases split with ⟨rfl, rfl⟩
            simp
  | cons symbol L₁ induction =>
      cases sourceValue : tapeStacks k₁ with
      | nil =>
          rw [sourceValue, splitAtPred] at split
          cases split
      | cons sourceHead sourceTail =>
          rw [sourceValue, splitAtPred] at split
          cases predicateValue : p sourceHead <;>
            simp only [predicateValue, cond_false, cond_true] at split
          · rcases recursiveSplit :
              splitAtPred p sourceTail with
              ⟨movedPrefix, found, suffix⟩
            rw [recursiveSplit] at split
            cases split
            let nextStacks :=
              Function.update
                (Function.update tapeStacks k₁ sourceTail)
                k₂ (symbol :: tapeStacks k₂)
            let middle : Cfg' :=
              ⟨some (Λ'.move p k₁ k₂ q), some symbol,
                nextStacks⟩
            have firstStep :
                TM2.step tr
                    ⟨some (Λ'.move p k₁ k₂ q), s,
                      tapeStacks⟩ =
                  some middle := by
              simp [middle, nextStacks, TM2.step, tr.eq_def,
                pop', push', sourceValue, predicateValue,
                Function.update_of_ne different.symm]
              rfl
            have spaceEq :
                TM2.stackSpace middle =
                  TM2.stackSpace
                    ⟨some (Λ'.move p k₁ k₂ q), s,
                      tapeStacks⟩ := by
              apply stackSpace_transfer_eq k₁ k₂ different
                symbol sourceTail tapeStacks sourceValue
            have first :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  (TM2.stackSpace
                    ⟨some (Λ'.move p k₁ k₂ q), s,
                      tapeStacks⟩)
                  ⟨some (Λ'.move p k₁ k₂ q), s,
                    tapeStacks⟩
                  middle := by
              apply EvalsToInSpace.single firstStep
              · exact Nat.le_refl _
              · exact spaceEq.le
            have recursiveSplit' :
                splitAtPred p (nextStacks k₁) =
                  (movedPrefix, found, suffix) := by
              simpa [nextStacks, different] using recursiveSplit
            have rest :=
              induction (tapeStacks := nextStacks)
                (s := some symbol) recursiveSplit'
            have rest' :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  (TM2.stackSpace
                    ⟨some (Λ'.move p k₁ k₂ q), s,
                      tapeStacks⟩)
                  middle
                  ⟨some q, found,
                    Function.update
                      (Function.update tapeStacks k₁ suffix) k₂
                      ((symbol :: movedPrefix).reverseAux
                        (tapeStacks k₂))⟩ := by
              convert rest.mono spaceEq.le using 1
              all_goals
                simp [nextStacks, Function.update_comm,
                  different, different.symm, List.reverseAux]
            exact first.trans rest'
          · cases split

/-- Clearing a prefix only removes stack cells. -/
def clear_ok_inSpace {p k q s L₁ o L₂}
    {tapeStacks : K' → List Γ'}
    (split :
      splitAtPred p (tapeStacks k) = (L₁, o, L₂)) :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      (TM2.stackSpace
        ⟨some (Λ'.clear p k q), s, tapeStacks⟩)
      ⟨some (Λ'.clear p k q), s, tapeStacks⟩
      ⟨some q, o, Function.update tapeStacks k L₂⟩ := by
  induction L₁ generalizing tapeStacks s with
  | nil =>
      have stepEq :
          TM2.step tr
              ⟨some (Λ'.clear p k q), s, tapeStacks⟩ =
            some
              ⟨some q, o, Function.update tapeStacks k L₂⟩ := by
        revert split
        cases sourceValue : tapeStacks k with
        | nil =>
            intro split
            simp only [splitAtPred] at split
            cases split
            simp [TM2.step, tr.eq_def, pop', sourceValue]
        | cons symbol sourceTail =>
            intro split
            simp only [splitAtPred] at split
            cases predicateValue : p symbol <;>
              simp only [predicateValue, cond_false, cond_true,
                Prod.mk.injEq, true_and, false_and,
                reduceCtorEq] at split
            rcases split with ⟨rfl, rfl⟩
            simp [TM2.step, tr.eq_def, pop', sourceValue,
              predicateValue]
      apply EvalsToInSpace.single stepEq
      · exact Nat.le_refl _
      · apply stackSpace_update_le
        revert split
        cases sourceValue : tapeStacks k with
        | nil =>
            intro split
            simp only [splitAtPred] at split
            cases split
            simp
        | cons symbol sourceTail =>
            intro split
            simp only [splitAtPred] at split
            cases predicateValue : p symbol <;>
              simp only [predicateValue, cond_false, cond_true,
                Prod.mk.injEq, true_and, false_and,
                reduceCtorEq] at split
            rcases split with ⟨rfl, rfl⟩
            simp
  | cons symbol L₁ induction =>
      cases sourceValue : tapeStacks k with
      | nil =>
          rw [sourceValue, splitAtPred] at split
          cases split
      | cons sourceHead sourceTail =>
          rw [sourceValue, splitAtPred] at split
          cases predicateValue : p sourceHead <;>
            simp only [predicateValue, cond_false, cond_true] at split
          · rcases recursiveSplit :
              splitAtPred p sourceTail with
              ⟨clearedPrefix, found, suffix⟩
            rw [recursiveSplit] at split
            cases split
            let nextStacks :=
              Function.update tapeStacks k sourceTail
            let middle : Cfg' :=
              ⟨some (Λ'.clear p k q), some symbol, nextStacks⟩
            have firstStep :
                TM2.step tr
                    ⟨some (Λ'.clear p k q), s, tapeStacks⟩ =
                  some middle := by
              simp [middle, nextStacks, TM2.step, tr.eq_def,
                pop', sourceValue, predicateValue]
              rfl
            have spaceLe :
                TM2.stackSpace middle ≤
                  TM2.stackSpace
                    ⟨some (Λ'.clear p k q), s,
                      tapeStacks⟩ := by
              apply stackSpace_update_le
              simp [sourceValue]
            have first :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  (TM2.stackSpace
                    ⟨some (Λ'.clear p k q), s,
                      tapeStacks⟩)
                  ⟨some (Λ'.clear p k q), s, tapeStacks⟩
                  middle := by
              apply EvalsToInSpace.single firstStep
              · exact Nat.le_refl _
              · exact spaceLe
            have recursiveSplit' :
                splitAtPred p (nextStacks k) =
                  (clearedPrefix, found, suffix) := by
              simpa [nextStacks] using recursiveSplit
            have rest :=
              induction (tapeStacks := nextStacks)
                (s := some symbol) recursiveSplit'
            have rest' :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  (TM2.stackSpace
                    ⟨some (Λ'.clear p k q), s,
                      tapeStacks⟩)
                  middle
                  ⟨some q, found,
                    Function.update tapeStacks k suffix⟩ := by
              convert rest.mono spaceLe using 1
              all_goals simp [nextStacks]
            exact first.trans rest'
          · cases split

/-- Moving the reverse stack back to the main stack preserves total space. -/
def unrev_ok_inSpace {q s} {tapeStacks : K' → List Γ'} :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      (TM2.stackSpace
        ⟨some (unrev q), s, tapeStacks⟩)
      ⟨some (unrev q), s, tapeStacks⟩
      ⟨some q, none,
        Function.update
          (Function.update tapeStacks .rev []) .main
          (List.reverseAux (tapeStacks .rev)
            (tapeStacks .main))⟩ := by
  exact move_ok_inSpace (by decide) (splitAtPred_false _)

/-- The evaluator's `copy` loop duplicates the reverse stack into the main
and continuation stacks.  At every intermediate point, its total space is at
most the final size: the original main and continuation data, the auxiliary
stack, and two copies of the reverse stack. -/
def copy_ok_inSpace (q s a b c d) :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      (a.length + 2 * b.length + c.length + d.length)
      ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
      ⟨some q, none,
        K'.elim (List.reverseAux b a) [] c
          (List.reverseAux b d)⟩ := by
  induction b generalizing a d s with
  | nil =>
      apply EvalsToInSpace.single
      · simp
      · rw [stackSpace_elim]
        simp
      · rw [stackSpace_elim]
        simp
  | cons symbol b induction =>
      let middle : Cfg' :=
        ⟨some (Λ'.copy q), some symbol,
          K'.elim (symbol :: a) b c (symbol :: d)⟩
      have firstStep :
          TM2.step tr
              ⟨some (Λ'.copy q), s,
                K'.elim a (symbol :: b) c d⟩ =
            some middle := by
        simp [middle, tr, pop', push']
        rfl
      have first :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            (a.length + 2 * (symbol :: b).length + c.length + d.length)
            ⟨some (Λ'.copy q), s,
              K'.elim a (symbol :: b) c d⟩
            middle := by
        apply EvalsToInSpace.single firstStep
        · rw [stackSpace_elim]
          simp
        · rw [stackSpace_elim]
          simp
          omega
      have rest :=
        induction (a := symbol :: a) (d := symbol :: d)
          (s := some symbol)
      have rest' :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            (a.length + 2 * (symbol :: b).length + c.length + d.length)
            middle
            ⟨some q, none,
              K'.elim (List.reverseAux (symbol :: b) a) [] c
                (List.reverseAux (symbol :: b) d)⟩ := by
        convert rest using 1
        all_goals simp [List.reverseAux] <;> omega
      exact first.trans rest'

end PartrecToTM2
end Turing
