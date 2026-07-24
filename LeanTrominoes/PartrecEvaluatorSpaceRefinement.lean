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

private theorem splitAtPred_length {α : Type*} (predicate : α → Bool) :
    ∀ values first found rest,
      splitAtPred predicate values = (first, found, rest) →
        values.length =
          first.length + found.toList.length + rest.length := by
  intro values
  induction values with
  | nil =>
      intro first found rest split
      simp only [splitAtPred] at split
      cases split
      rfl
  | cons value values induction =>
      intro first found rest split
      rw [splitAtPred] at split
      cases predicateValue : predicate value
      · rcases recursiveSplit :
          splitAtPred predicate values with
          ⟨recursiveFirst, recursivePair⟩
        rcases recursivePair with ⟨recursiveFound, recursiveRest⟩
        simp only [predicateValue, cond_false, recursiveSplit] at split
        cases split
        have recursiveLength :=
          induction recursiveFirst found rest
            recursiveSplit
        simp only [List.length_cons]
        omega
      · simp only [predicateValue, cond_true] at split
        cases split
        simp
        omega

/-- The two-pass stable move used by continuation shuffling preserves total
space throughout, including the optional delimiter restored between passes. -/
def move₂_ok_inSpace {p k₁ k₂ q s L₁ o L₂}
    {tapeStacks : K' → List Γ'}
    (different : k₁ ≠ .rev ∧ k₂ ≠ .rev ∧ k₁ ≠ k₂)
    (reverseEmpty : tapeStacks .rev = [])
    (split :
      splitAtPred p (tapeStacks k₁) = (L₁, o, L₂)) :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      (TM2.stackSpace
        ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩)
      ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩
      ⟨some q, none,
        Function.update
          (Function.update tapeStacks k₁
            (o.elim id List.cons L₂))
          k₂ (L₁ ++ tapeStacks k₂)⟩ := by
  let afterFirstStacks :=
    Function.update
      (Function.update tapeStacks k₁ L₂) .rev
      (L₁.reverseAux (tapeStacks .rev))
  let afterFirst : Cfg' :=
    ⟨some (Λ'.push k₁ id
      (Λ'.move (fun _ => false) .rev k₂ q)),
      o, afterFirstStacks⟩
  have firstRaw :=
    move_ok_inSpace
      (q := Λ'.push k₁ id
        (Λ'.move (fun _ => false) .rev k₂ q))
      (s := s) different.1 split
  have first :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        (TM2.stackSpace
          ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩)
        ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩
        afterFirst := by
    simpa [move₂, moveExcl, afterFirst, afterFirstStacks] using firstRaw
  let restored := o.elim id List.cons L₂
  let afterPushStacks :=
    Function.update afterFirstStacks k₁ restored
  let afterPush : Cfg' :=
    ⟨some (Λ'.move (fun _ => false) .rev k₂ q),
      o, afterPushStacks⟩
  have pushStep :
      TM2.step tr afterFirst = some afterPush := by
    cases o <;>
      simp [afterFirst, afterPush, afterPushStacks, restored,
        TM2.step, tr.eq_def, afterFirstStacks,
        Function.update_comm, Function.update_idem,
        different.1, different.1.symm]
    all_goals rfl
  have splitLength := splitAtPred_length p _ _ _ _ split
  have pushSpace :
      TM2.stackSpace afterPush =
        TM2.stackSpace
          ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩ := by
    rw [stackSpace_fields, stackSpace_fields]
    cases k₁ <;> cases o <;>
      simp_all [afterPush, afterPushStacks, afterFirstStacks,
        restored, Function.update,
        List.reverseAux_eq] <;> omega
  have push :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        (TM2.stackSpace
          ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩)
        afterFirst afterPush := by
    apply EvalsToInSpace.single pushStep
    · exact first.last_le
    · exact pushSpace.le
  have reverseNow :
      afterPushStacks .rev = L₁.reverse := by
    simp [afterPushStacks, afterFirstStacks,
      different.1.symm, reverseEmpty, List.reverseAux_eq]
  have secondRaw :=
    move_ok_inSpace (q := q) (s := o)
      (tapeStacks := afterPushStacks) different.2.1.symm
      (splitAtPred_false (afterPushStacks .rev))
  have second :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        (TM2.stackSpace
          ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩)
        afterPush
        ⟨some q, none,
          Function.update
            (Function.update tapeStacks k₁ restored)
            k₂ (L₁ ++ tapeStacks k₂)⟩ := by
    have secondBound :
        TM2.stackSpace afterPush ≤
          TM2.stackSpace
            ⟨some (move₂ p k₁ k₂ q), s, tapeStacks⟩ :=
      pushSpace.le
    convert secondRaw.mono secondBound using 1
    all_goals
      simp [afterPushStacks, afterFirstStacks,
        reverseEmpty, restored, Function.update_comm,
        different.1, different.2.2, List.reverseAux_eq]
    ext stackIndex
    cases k₁ <;> cases k₂ <;> cases stackIndex <;>
      simp_all [afterPushStacks, afterFirstStacks, restored,
        Function.update, List.reverseAux_eq]
  exact (first.trans push).trans second

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

/-- Reading the first natural from the main stack uses at most one cell beyond
the input configuration; this extra cell is the delimiter of the synthesized
zero when the input list is empty. -/
def head_main_ok_inSpace {q s L} {c d : List Γ'} :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      ((trList L).length + c.length + d.length + 1)
      ⟨some (head .main q), s,
        K'.elim (trList L) [] c d⟩
      ⟨some q, none,
        K'.elim (trList [L.headI]) [] c d⟩ := by
  let delimiter : Option Γ' :=
    List.casesOn L none fun _ _ => some Γ'.cons
  let afterMove : Cfg' :=
    ⟨some
        (Λ'.push .rev (fun _ => some Γ'.cons)
          (Λ'.read fun state =>
            (if state = some Γ'.consₗ
              then id
              else Λ'.clear
                (fun symbol => symbol = Γ'.consₗ) .main)
              (unrev q))),
      delimiter,
      K'.elim (trList L.tail)
        (List.reverse (trNat L.headI)) c d⟩
  have headSplit :
      splitAtPred natEnd (trList L) =
        (trNat L.headI, delimiter, trList L.tail) := by
    apply splitAtPred_eq
    · exact trNat_natEnd _
    · cases L <;> simp [delimiter]
  have moveRaw :=
    move_ok_inSpace
      (p := natEnd) (k₁ := .main) (k₂ := .rev)
      (q := Λ'.push .rev (fun _ => some Γ'.cons)
        (Λ'.read fun state =>
          (if state = some Γ'.consₗ
            then id
            else Λ'.clear
              (fun symbol => symbol = Γ'.consₗ) .main)
            (unrev q)))
      (s := s)
      (tapeStacks := K'.elim (trList L) [] c d)
      (by decide) headSplit
  have startSpace :
      TM2.stackSpace
          ⟨some (head .main q), s,
            K'.elim (trList L) [] c d⟩ ≤
        (trList L).length + c.length + d.length + 1 := by
    rw [stackSpace_elim]
    simp
  have move :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        ((trList L).length + c.length + d.length + 1)
        ⟨some (head .main q), s,
          K'.elim (trList L) [] c d⟩
        afterMove := by
    convert moveRaw.mono startSpace using 1
    all_goals
      simp [head, afterMove, delimiter, List.reverseAux_eq]
  let afterPush : Cfg' :=
    ⟨some
        (Λ'.read fun state =>
          (if state = some Γ'.consₗ
            then id
            else Λ'.clear
              (fun symbol => symbol = Γ'.consₗ) .main)
            (unrev q)),
      delimiter,
      K'.elim (trList L.tail)
        (Γ'.cons :: List.reverse (trNat L.headI)) c d⟩
  have pushStep :
      TM2.step tr afterMove = some afterPush := by
    simp [afterMove, afterPush, TM2.step, tr.eq_def]
    rfl
  have pushSpace :
      TM2.stackSpace afterPush ≤
        (trList L).length + c.length + d.length + 1 := by
    rw [stackSpace_elim]
    cases L <;>
      simp [trList] <;> omega
  have push :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        ((trList L).length + c.length + d.length + 1)
        afterMove afterPush :=
    EvalsToInSpace.single pushStep move.last_le pushSpace
  let afterRead : Cfg' :=
    ⟨some
        (Λ'.clear (fun symbol => symbol = Γ'.consₗ)
          .main (unrev q)),
      delimiter,
      K'.elim (trList L.tail)
        (Γ'.cons :: List.reverse (trNat L.headI)) c d⟩
  have readStep :
      TM2.step tr afterPush = some afterRead := by
    cases L <;>
      simp [afterPush, afterRead, delimiter, TM2.step, tr.eq_def]
    all_goals rfl
  have read :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        ((trList L).length + c.length + d.length + 1)
        afterPush afterRead :=
    EvalsToInSpace.single readStep pushSpace (by
      rw [stackSpace_fields]
      rw [stackSpace_fields] at pushSpace
      exact pushSpace)
  have clearSplit :
      splitAtPred (fun symbol => symbol = Γ'.consₗ)
          (trList L.tail) =
        (trList L.tail, none, []) := by
    apply splitAtPred_eq
    · exact fun symbol member =>
        Bool.decide_false (trList_ne_consₗ _ _ member)
    · exact ⟨rfl, rfl⟩
  have clearRaw :=
    clear_ok_inSpace
      (p := fun symbol => symbol = Γ'.consₗ)
      (k := .main)
      (L₁ := trList L.tail) (o := none) (L₂ := [])
      (q := unrev q) (s := delimiter)
      (tapeStacks :=
        K'.elim (trList L.tail)
          (Γ'.cons :: List.reverse (trNat L.headI)) c d)
      clearSplit
  let afterClear : Cfg' :=
    ⟨some (unrev q), none,
      K'.elim [] (Γ'.cons :: List.reverse (trNat L.headI)) c d⟩
  have clear :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        ((trList L).length + c.length + d.length + 1)
        afterRead afterClear := by
    have readSpace :
        TM2.stackSpace afterRead ≤
          (trList L).length + c.length + d.length + 1 := by
      rw [stackSpace_fields]
      rw [stackSpace_fields] at pushSpace
      exact pushSpace
    convert clearRaw.mono readSpace using 1
    all_goals simp [afterClear]
  have unreverseRaw :=
    unrev_ok_inSpace
      (q := q) (s := none)
      (tapeStacks :=
        K'.elim [] (Γ'.cons :: List.reverse (trNat L.headI)) c d)
  have clearSpace := clear.last_le
  have unreverse :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        ((trList L).length + c.length + d.length + 1)
        afterClear
        ⟨some q, none,
          K'.elim (trList [L.headI]) [] c d⟩ := by
    convert unreverseRaw.mono clearSpace using 1
    all_goals
      simp [List.reverseAux_eq]
  exact (((move.trans push).trans read).trans clear).trans unreverse

/-- Reading the first natural from the continuation stack never exceeds the
input footprint.  The outer list delimiter that is consumed from the
continuation stack pays for the delimiter inserted after the extracted
natural on the main stack. -/
def head_stack_ok_inSpace {q s L₁ L₂ L₃} :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      ((trList L₁).length + (trList L₂).length + L₃.length + 1)
      ⟨some (head .stack q), s,
        K'.elim (trList L₁) [] []
          (trList L₂ ++ Γ'.consₗ :: L₃)⟩
      ⟨some q, none,
        K'.elim (trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  cases L₂ with
  | nil =>
      let afterMove : Cfg' :=
        ⟨some
            (Λ'.push .rev (fun _ => some Γ'.cons)
              (Λ'.read fun state =>
                (if state = some Γ'.consₗ
                  then id
                  else Λ'.clear
                    (fun symbol => symbol = Γ'.consₗ) .stack)
                  (unrev q))),
          some Γ'.consₗ,
          K'.elim (trList L₁) [] [] L₃⟩
      have moveRaw :=
        move_ok_inSpace
          (p := natEnd) (k₁ := .stack) (k₂ := .rev)
          (q := Λ'.push .rev (fun _ => some Γ'.cons)
            (Λ'.read fun state =>
              (if state = some Γ'.consₗ
                then id
                else Λ'.clear
                  (fun symbol => symbol = Γ'.consₗ) .stack)
                (unrev q)))
          (s := s)
          (tapeStacks :=
            K'.elim (trList L₁) [] []
              (trList [] ++ Γ'.consₗ :: L₃))
          (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃
            (by rintro _ ⟨⟩) ⟨rfl, rfl⟩)
      have move :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length + (trList []).length +
              L₃.length + 1)
            ⟨some (head .stack q), s,
              K'.elim (trList L₁) [] []
                (trList [] ++ Γ'.consₗ :: L₃)⟩
            afterMove := by
        convert moveRaw using 1
        all_goals
          simp [head, afterMove, stackSpace_elim] <;> omega
      let afterPush : Cfg' :=
        ⟨some
            (Λ'.read fun state =>
              (if state = some Γ'.consₗ
                then id
                else Λ'.clear
                  (fun symbol => symbol = Γ'.consₗ) .stack)
                (unrev q)),
          some Γ'.consₗ,
          K'.elim (trList L₁) [Γ'.cons] [] L₃⟩
      have pushStep :
          TM2.step tr afterMove = some afterPush := by
        simp [afterMove, afterPush, TM2.step, tr.eq_def]
        rfl
      have pushSpace :
          TM2.stackSpace afterPush ≤
            (trList L₁).length + (trList []).length +
              L₃.length + 1 := by
        rw [stackSpace_elim]
        simp
        omega
      have push :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length + (trList []).length +
              L₃.length + 1)
            afterMove afterPush :=
        EvalsToInSpace.single pushStep move.last_le pushSpace
      let afterRead : Cfg' :=
        ⟨some (unrev q), some Γ'.consₗ,
          K'.elim (trList L₁) [Γ'.cons] [] L₃⟩
      have readStep :
          TM2.step tr afterPush = some afterRead := by
        simp [afterPush, afterRead, TM2.step, tr.eq_def]
        rfl
      have read :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length + (trList []).length +
              L₃.length + 1)
            afterPush afterRead :=
        EvalsToInSpace.single readStep pushSpace (by
          rw [stackSpace_fields]
          rw [stackSpace_fields] at pushSpace
          exact pushSpace)
      have unreverseRaw :=
        unrev_ok_inSpace
          (q := q) (s := some Γ'.consₗ)
          (tapeStacks :=
            K'.elim (trList L₁) [Γ'.cons] [] L₃)
      have unreverse :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length + (trList []).length +
              L₃.length + 1)
            afterRead
            ⟨some q, none,
              K'.elim (trList ([].headI :: L₁)) [] [] L₃⟩ := by
        convert unreverseRaw.mono read.last_le using 1
        all_goals
          simp [List.reverseAux_eq]
      exact (move.trans push).trans (read.trans unreverse)
  | cons value tail =>
      let afterMove : Cfg' :=
        ⟨some
            (Λ'.push .rev (fun _ => some Γ'.cons)
              (Λ'.read fun state =>
                (if state = some Γ'.consₗ
                  then id
                  else Λ'.clear
                    (fun symbol => symbol = Γ'.consₗ) .stack)
                  (unrev q))),
          some Γ'.cons,
          K'.elim (trList L₁)
            (List.reverse (trNat value)) []
            (trList tail ++ Γ'.consₗ :: L₃)⟩
      have moveRaw :=
        move_ok_inSpace
          (p := natEnd) (k₁ := .stack) (k₂ := .rev)
          (q := Λ'.push .rev (fun _ => some Γ'.cons)
            (Λ'.read fun state =>
              (if state = some Γ'.consₗ
                then id
                else Λ'.clear
                  (fun symbol => symbol = Γ'.consₗ) .stack)
                (unrev q)))
          (s := s)
          (tapeStacks :=
            K'.elim (trList L₁) [] []
              (trList (value :: tail) ++ Γ'.consₗ :: L₃))
          (by decide)
          (splitAtPred_eq _ _
            (trNat value) (some Γ'.cons)
            (trList tail ++ Γ'.consₗ :: L₃)
            (trNat_natEnd _) ⟨rfl, by simp⟩)
      have move :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length +
              (trList (value :: tail)).length + L₃.length + 1)
            ⟨some (head .stack q), s,
              K'.elim (trList L₁) [] []
                (trList (value :: tail) ++ Γ'.consₗ :: L₃)⟩
            afterMove := by
        convert moveRaw using 1
        all_goals
          simp [head, afterMove, stackSpace_elim,
            List.reverseAux_eq] <;> omega
      let afterPush : Cfg' :=
        ⟨some
            (Λ'.read fun state =>
              (if state = some Γ'.consₗ
                then id
                else Λ'.clear
                  (fun symbol => symbol = Γ'.consₗ) .stack)
                (unrev q)),
          some Γ'.cons,
          K'.elim (trList L₁)
            (Γ'.cons :: List.reverse (trNat value)) []
            (trList tail ++ Γ'.consₗ :: L₃)⟩
      have pushStep :
          TM2.step tr afterMove = some afterPush := by
        simp [afterMove, afterPush, TM2.step, tr.eq_def]
        rfl
      have pushSpace :
          TM2.stackSpace afterPush ≤
            (trList L₁).length +
              (trList (value :: tail)).length + L₃.length + 1 := by
        rw [stackSpace_elim]
        simp
        omega
      have push :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length +
              (trList (value :: tail)).length + L₃.length + 1)
            afterMove afterPush :=
        EvalsToInSpace.single pushStep move.last_le pushSpace
      let afterRead : Cfg' :=
        ⟨some
            (Λ'.clear (fun symbol => symbol = Γ'.consₗ)
              .stack (unrev q)),
          some Γ'.cons,
          K'.elim (trList L₁)
            (Γ'.cons :: List.reverse (trNat value)) []
            (trList tail ++ Γ'.consₗ :: L₃)⟩
      have readStep :
          TM2.step tr afterPush = some afterRead := by
        simp [afterPush, afterRead, TM2.step, tr.eq_def]
        rfl
      have read :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length +
              (trList (value :: tail)).length + L₃.length + 1)
            afterPush afterRead :=
        EvalsToInSpace.single readStep pushSpace (by
          rw [stackSpace_fields]
          rw [stackSpace_fields] at pushSpace
          exact pushSpace)
      have clearRaw :=
        clear_ok_inSpace
          (p := fun symbol => symbol = Γ'.consₗ)
          (k := .stack)
          (L₁ := trList tail) (o := some Γ'.consₗ) (L₂ := L₃)
          (q := unrev q) (s := some Γ'.cons)
          (tapeStacks :=
            K'.elim (trList L₁)
              (Γ'.cons :: List.reverse (trNat value)) []
              (trList tail ++ Γ'.consₗ :: L₃))
          (splitAtPred_eq _ _
            (trList tail) (some Γ'.consₗ) L₃
            (fun symbol member =>
              Bool.decide_false
                (trList_ne_consₗ _ _ member))
            ⟨rfl, by simp⟩)
      let afterClear : Cfg' :=
        ⟨some (unrev q), some Γ'.consₗ,
          K'.elim (trList L₁)
            (Γ'.cons :: List.reverse (trNat value)) [] L₃⟩
      have clear :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length +
              (trList (value :: tail)).length + L₃.length + 1)
            afterRead afterClear := by
        convert clearRaw.mono read.last_le using 1
        all_goals simp [afterClear]
      have unreverseRaw :=
        unrev_ok_inSpace
          (q := q) (s := some Γ'.consₗ)
          (tapeStacks :=
            K'.elim (trList L₁)
              (Γ'.cons :: List.reverse (trNat value)) [] L₃)
      have unreverse :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ((trList L₁).length +
              (trList (value :: tail)).length + L₃.length + 1)
            afterClear
            ⟨some q, none,
              K'.elim
                (trList ((value :: tail).headI :: L₁))
                [] [] L₃⟩ := by
        convert unreverseRaw.mono clear.last_le using 1
        all_goals
          simp [List.reverseAux_eq]
      exact (((move.trans push).trans read).trans clear).trans unreverse

/-- Binary successor uses at most one additional stack cell, exactly the
possible new high bit when incrementing an all-ones input. -/
noncomputable def succ_ok_inSpace {q s n} {c d : List Γ'} :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace
      ((trList [n]).length + c.length + d.length + 1)
      ⟨some (Λ'.succ q), s,
        K'.elim (trList [n]) [] c d⟩
      ⟨some q, none,
        K'.elim (trList [n.succ]) [] c d⟩ := by
  simp only [trList, trNat.eq_1, Nat.cast_succ, Num.add_one]
  cases number : (n : Num) with
  | zero =>
      have inputZero : n = 0 := by
        have converted :=
          congrArg (fun value : Num => (value : Nat)) number
        simpa using converted
      subst n
      clear number
      let afterSucc : Cfg' :=
        ⟨some (unrev q), some Γ'.cons,
          K'.elim [Γ'.bit1, Γ'.cons] [] c d⟩
      have succStep :
          TM2.step tr
              ⟨some (Λ'.succ q), s,
                K'.elim [Γ'.cons] [] c d⟩ =
            some afterSucc := by
        simp [afterSucc, TM2.step, tr.eq_def]
        rfl
      have first :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ([Γ'.cons].length + c.length + d.length + 1)
            ⟨some (Λ'.succ q), s,
              K'.elim [Γ'.cons] [] c d⟩
            afterSucc := by
        apply EvalsToInSpace.single succStep
        · rw [stackSpace_elim]
          simp
        · rw [stackSpace_elim]
          simp
          omega
      have unreverseRaw :=
        unrev_ok_inSpace
          (q := q) (s := some Γ'.cons)
          (tapeStacks :=
            K'.elim [Γ'.bit1, Γ'.cons] [] c d)
      have unreverse :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace
            ([Γ'.cons].length + c.length + d.length + 1)
            afterSucc
            ⟨some q, none,
              K'.elim [Γ'.bit1, Γ'.cons] [] c d⟩ := by
        convert unreverseRaw.mono first.last_le using 1
        all_goals simp
      exact first.trans unreverse
  | pos positive =>
      have inputPositive : n = (positive : Nat) := by
        have converted :=
          congrArg (fun value : Num => (value : Nat)) number
        simpa using converted
      subst n
      clear number
      suffices
          ∀ reversePrefix,
            Σ finalReverse finalMain finalState,
              PLift
                (List.reverseAux reversePrefix
                    (trPosNum positive.succ) =
                  List.reverseAux finalReverse finalMain) ×
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum positive).length + 1 +
                  reversePrefix.length + c.length + d.length + 1)
                ⟨some (Λ'.succ q), s,
                  K'.elim
                    (trPosNum positive ++ [Γ'.cons])
                    reversePrefix c d⟩
                ⟨some (unrev q), finalState,
                  K'.elim
                    (finalMain ++ [Γ'.cons])
                    finalReverse c d⟩ by
        obtain ⟨finalReverse, finalMain, finalState,
          representationLift, increment⟩ := this []
        have representation := representationLift.down
        have increment' :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace
              ((trPosNum positive).length + 1 +
                c.length + d.length + 1)
              ⟨some (Λ'.succ q), s,
                K'.elim
                  (trPosNum positive ++ [Γ'.cons])
                  [] c d⟩
              ⟨some (unrev q), finalState,
                K'.elim
                  (finalMain ++ [Γ'.cons])
                  finalReverse c d⟩ := by
          simpa using increment
        have unreverseRaw :=
          unrev_ok_inSpace
            (q := q) (s := finalState)
            (tapeStacks :=
              K'.elim
                (finalMain ++ [Γ'.cons])
                finalReverse c d)
        have outputEq :
            List.reverseAux finalReverse
                (finalMain ++ [Γ'.cons]) =
              trPosNum positive.succ ++ [Γ'.cons] := by
          simp only [List.reverseAux_eq, List.reverse_nil,
            List.nil_append] at representation
          rw [List.reverseAux_eq, ← List.append_assoc,
            ← representation]
        have outputEq' :
            finalReverse.reverse ++
                (finalMain ++ [Γ'.cons]) =
              trPosNum positive.succ ++ [Γ'.cons] := by
          simpa [List.reverseAux_eq] using outputEq
        have unreverse :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace
              ((trPosNum positive).length + 1 +
                c.length + d.length + 1)
              ⟨some (unrev q), finalState,
                K'.elim
                  (finalMain ++ [Γ'.cons])
                  finalReverse c d⟩
              ⟨some q, none,
                K'.elim
                  (trPosNum positive.succ ++ [Γ'.cons])
                  [] c d⟩ := by
          convert unreverseRaw.mono increment'.last_le using 1
          all_goals
            simp [outputEq']
        have run := increment'.trans unreverse
        simpa [trNum, Num.succ, Num.succ'] using run
      induction positive generalizing s with
      | one =>
          intro reversePrefix
          let middle : Cfg' :=
            ⟨some (Λ'.succ q), some Γ'.bit1,
              K'.elim [Γ'.cons]
                (Γ'.bit0 :: reversePrefix) c d⟩
          let afterSucc : Cfg' :=
            ⟨some (unrev q), some Γ'.cons,
              K'.elim [Γ'.bit1, Γ'.cons]
                (Γ'.bit0 :: reversePrefix) c d⟩
          have firstStep :
              TM2.step tr
                  ⟨some (Λ'.succ q), s,
                    K'.elim
                      (trPosNum PosNum.one ++ [Γ'.cons])
                      reversePrefix c d⟩ =
                some middle := by
            simp [middle, trPosNum, TM2.step, tr.eq_def]
            rfl
          have first :
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum PosNum.one).length + 1 +
                  reversePrefix.length + c.length + d.length + 1)
                ⟨some (Λ'.succ q), s,
                  K'.elim
                    (trPosNum PosNum.one ++ [Γ'.cons])
                    reversePrefix c d⟩
                middle := by
            apply EvalsToInSpace.single firstStep
            · rw [stackSpace_elim]
              simp [trPosNum]
            · rw [stackSpace_elim]
              simp [trPosNum]
              omega
          have secondStep :
              TM2.step tr middle = some afterSucc := by
            simp [middle, afterSucc, TM2.step, tr.eq_def]
            rfl
          have second :
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum PosNum.one).length + 1 +
                  reversePrefix.length + c.length + d.length + 1)
                middle afterSucc := by
            apply EvalsToInSpace.single secondStep
            · exact first.last_le
            · rw [stackSpace_elim]
              simp [trPosNum]
              omega
          exact
            ⟨Γ'.bit0 :: reversePrefix, [Γ'.bit1],
              some Γ'.cons, ⟨rfl⟩, first.trans second⟩
      | bit1 smaller induction =>
          intro reversePrefix
          let middle : Cfg' :=
            ⟨some (Λ'.succ q), some Γ'.bit1,
              K'.elim
                (trPosNum smaller ++ [Γ'.cons])
                (Γ'.bit0 :: reversePrefix) c d⟩
          have firstStep :
              TM2.step tr
                  ⟨some (Λ'.succ q), s,
                    K'.elim
                      (trPosNum (PosNum.bit1 smaller) ++
                        [Γ'.cons])
                      reversePrefix c d⟩ =
                some middle := by
            simp [middle, trPosNum, TM2.step, tr.eq_def]
            rfl
          have first :
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum (PosNum.bit1 smaller)).length + 1 +
                  reversePrefix.length + c.length + d.length + 1)
                ⟨some (Λ'.succ q), s,
                  K'.elim
                    (trPosNum (PosNum.bit1 smaller) ++
                      [Γ'.cons])
                    reversePrefix c d⟩
                middle := by
            apply EvalsToInSpace.single firstStep
            · rw [stackSpace_elim]
              simp [trPosNum]
            · rw [stackSpace_elim]
              simp [trPosNum]
              omega
          obtain ⟨finalReverse, finalMain, finalState,
            representation, rest⟩ :=
              induction (s := some Γ'.bit1)
                (Γ'.bit0 :: reversePrefix)
          have rest' :
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum (PosNum.bit1 smaller)).length + 1 +
                  reversePrefix.length + c.length + d.length + 1)
                middle
                ⟨some (unrev q), finalState,
                  K'.elim
                    (finalMain ++ [Γ'.cons])
                    finalReverse c d⟩ := by
            simpa [middle, trPosNum, Nat.add_assoc,
              Nat.add_left_comm, Nat.add_comm] using rest
          exact
            ⟨finalReverse, finalMain, finalState,
              representation, first.trans rest'⟩
      | bit0 smaller induction =>
          intro reversePrefix
          let afterSucc : Cfg' :=
            ⟨some (unrev q), some Γ'.bit0,
              K'.elim
                (Γ'.bit1 :: trPosNum smaller ++ [Γ'.cons])
                reversePrefix c d⟩
          have succStep :
              TM2.step tr
                  ⟨some (Λ'.succ q), s,
                    K'.elim
                      (trPosNum (PosNum.bit0 smaller) ++
                        [Γ'.cons])
                      reversePrefix c d⟩ =
                some afterSucc := by
            simp [afterSucc, trPosNum, TM2.step, tr.eq_def]
            rfl
          have run :
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum (PosNum.bit0 smaller)).length + 1 +
                  reversePrefix.length + c.length + d.length + 1)
                ⟨some (Λ'.succ q), s,
                  K'.elim
                    (trPosNum (PosNum.bit0 smaller) ++
                      [Γ'.cons])
                    reversePrefix c d⟩
                afterSucc := by
            apply EvalsToInSpace.single succStep
            · rw [stackSpace_elim]
              simp [trPosNum]
            · rw [stackSpace_elim]
              simp [trPosNum]
          exact
            ⟨reversePrefix, trPosNum (PosNum.bit1 smaller),
              some Γ'.bit0, ⟨rfl⟩, by
                simpa [afterSucc, trPosNum] using run⟩

/-- Binary predecessor never increases the total stack footprint.  The
certificate also covers the empty-list and zero-head branches used by the
partial-recursive evaluator's case instruction. -/
noncomputable def pred_ok_inSpace (q₁ q₂ s v)
    (c d : List Γ') :
    Σ finalState,
      EvalsToInSpace (TM2.step tr) TM2.stackSpace
        ((trList v).length + c.length + d.length)
        ⟨some (Λ'.pred q₁ q₂), s,
          K'.elim (trList v) [] c d⟩
        (v.headI.rec
          ⟨some q₁, finalState,
            K'.elim (trList v.tail) [] c d⟩
          fun n _ =>
            ⟨some q₂, finalState,
              K'.elim (trList (n :: v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, tail⟩)
  · refine ⟨none, EvalsToInSpace.single ?_ ?_ ?_⟩
    · simp
    · rw [stackSpace_elim]
      simp
    · change
        TM2.stackSpace
            ⟨some q₁, none, K'.elim [] [] c d⟩ ≤
          (trList []).length + c.length + d.length
      rw [stackSpace_elim]
      simp
  · refine
      ⟨some Γ'.cons,
        EvalsToInSpace.single ?_ ?_ ?_⟩
    · simp
    · rw [stackSpace_elim]
      simp
    · simp only [List.headI_cons, Nat.rec_zero,
        List.tail_cons]
      rw [stackSpace_elim]
      simp
  · simp only [trList, trNat.eq_1, trNum, Nat.cast_succ,
      Num.add_one, Num.succ, List.tail_cons, List.headI_cons]
    cases number : (n : Num) with
    | zero =>
        have inputZero : n = 0 := by
          have converted :=
            congrArg (fun value : Num => (value : Nat)) number
          simpa using converted
        subst n
        clear number
        let afterPred : Cfg' :=
          ⟨some (unrev q₂), some Γ'.cons,
            K'.elim (Γ'.cons :: trList tail) [] c d⟩
        have predStep :
            TM2.step tr
                ⟨some (Λ'.pred q₁ q₂), s,
                  K'.elim
                    ([Γ'.bit1, Γ'.cons] ++ trList tail)
                    [] c d⟩ =
              some afterPred := by
          simp [afterPred, TM2.step, tr.eq_def]
          rfl
        have first :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace
              (([Γ'.bit1, Γ'.cons] ++
                  trList tail).length +
                c.length + d.length)
              ⟨some (Λ'.pred q₁ q₂), s,
                K'.elim
                  ([Γ'.bit1, Γ'.cons] ++ trList tail)
                  [] c d⟩
              afterPred := by
          apply EvalsToInSpace.single predStep
          · rw [stackSpace_elim]
            simp
          · rw [stackSpace_elim]
            simp
        have unreverseRaw :=
          unrev_ok_inSpace
            (q := q₂) (s := some Γ'.cons)
            (tapeStacks :=
              K'.elim (Γ'.cons :: trList tail) [] c d)
        have unreverse :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace
              (([Γ'.bit1, Γ'.cons] ++
                  trList tail).length +
                c.length + d.length)
              afterPred
              ⟨some q₂, none,
                K'.elim (Γ'.cons :: trList tail) [] c d⟩ := by
          convert unreverseRaw.mono first.last_le using 1
          all_goals simp
        exact ⟨none, by
          simpa [Num.succ', trPosNum, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using
              first.trans unreverse⟩
    | pos positive =>
        have inputPositive : n = (positive : Nat) := by
          have converted :=
            congrArg (fun value : Num => (value : Nat)) number
          simpa using converted
        subst n
        clear number
        suffices
            ∀ reversePrefix,
              Σ finalReverse finalMain finalState,
                PLift
                  (List.reverseAux reversePrefix
                      (trPosNum positive) =
                    List.reverseAux finalReverse finalMain) ×
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  ((trPosNum positive.succ).length + 1 +
                    (trList tail).length +
                    reversePrefix.length + c.length + d.length)
                  ⟨some (Λ'.pred q₁ q₂), s,
                    K'.elim
                      (trPosNum positive.succ ++
                        Γ'.cons :: trList tail)
                      reversePrefix c d⟩
                  ⟨some (unrev q₂), finalState,
                    K'.elim
                      (finalMain ++ Γ'.cons :: trList tail)
                      finalReverse c d⟩ by
          obtain ⟨finalReverse, finalMain, finalState,
            representationLift, decrement⟩ := this []
          have representation := representationLift.down
          have decrement' :
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum positive.succ).length + 1 +
                  (trList tail).length + c.length + d.length)
                ⟨some (Λ'.pred q₁ q₂), s,
                  K'.elim
                    (trPosNum positive.succ ++
                      Γ'.cons :: trList tail)
                    [] c d⟩
                ⟨some (unrev q₂), finalState,
                  K'.elim
                    (finalMain ++ Γ'.cons :: trList tail)
                    finalReverse c d⟩ := by
            simpa using decrement
          have unreverseRaw :=
            unrev_ok_inSpace
              (q := q₂) (s := finalState)
              (tapeStacks :=
                K'.elim
                  (finalMain ++ Γ'.cons :: trList tail)
                  finalReverse c d)
          have outputEq :
              List.reverseAux finalReverse
                  (finalMain ++ Γ'.cons :: trList tail) =
                trPosNum positive ++
                  Γ'.cons :: trList tail := by
            simp only [List.reverseAux_eq, List.reverse_nil,
              List.nil_append] at representation
            rw [List.reverseAux_eq, ← List.append_assoc,
              ← representation]
          have outputEq' :
              finalReverse.reverse ++
                  (finalMain ++ Γ'.cons :: trList tail) =
                trPosNum positive ++
                  Γ'.cons :: trList tail := by
            simpa [List.reverseAux_eq] using outputEq
          have unreverse :
              EvalsToInSpace (TM2.step tr) TM2.stackSpace
                ((trPosNum positive.succ).length + 1 +
                  (trList tail).length + c.length + d.length)
                ⟨some (unrev q₂), finalState,
                  K'.elim
                    (finalMain ++ Γ'.cons :: trList tail)
                    finalReverse c d⟩
                ⟨some q₂, none,
                  K'.elim
                    (trPosNum positive ++
                      Γ'.cons :: trList tail)
                    [] c d⟩ := by
            convert
              unreverseRaw.mono decrement'.last_le using 1
            all_goals simp [outputEq']
          exact ⟨none, by
            simpa [trNum, Num.succ, Num.succ',
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              decrement'.trans unreverse⟩
        induction positive generalizing s with
        | one =>
            intro reversePrefix
            let middle : Cfg' :=
              ⟨some (Λ'.pred q₁ q₂), some Γ'.bit0,
                K'.elim
                  (Γ'.bit1 :: Γ'.cons :: trList tail)
                  (Γ'.bit1 :: reversePrefix) c d⟩
            let afterPred : Cfg' :=
              ⟨some (unrev q₂), some Γ'.cons,
                K'.elim (Γ'.cons :: trList tail)
                  (Γ'.bit1 :: reversePrefix) c d⟩
            have firstStep :
                TM2.step tr
                    ⟨some (Λ'.pred q₁ q₂), s,
                      K'.elim
                        (trPosNum PosNum.one.succ ++
                          Γ'.cons :: trList tail)
                        reversePrefix c d⟩ =
                  some middle := by
              simp [middle, TM2.step, tr.eq_def]
              rfl
            have first :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  ((trPosNum PosNum.one.succ).length + 1 +
                    (trList tail).length +
                    reversePrefix.length + c.length + d.length)
                  ⟨some (Λ'.pred q₁ q₂), s,
                    K'.elim
                      (trPosNum PosNum.one.succ ++
                        Γ'.cons :: trList tail)
                      reversePrefix c d⟩
                  middle := by
              apply EvalsToInSpace.single firstStep
              · rw [stackSpace_elim]
                simp [PosNum.succ, trPosNum]
                omega
              · rw [stackSpace_elim]
                simp [PosNum.succ, trPosNum]
                omega
            have secondStep :
                TM2.step tr middle = some afterPred := by
              simp [middle, afterPred, TM2.step, tr.eq_def]
              rfl
            have second :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  ((trPosNum PosNum.one.succ).length + 1 +
                    (trList tail).length +
                    reversePrefix.length + c.length + d.length)
                  middle afterPred := by
              apply EvalsToInSpace.single secondStep
              · exact first.last_le
              · rw [stackSpace_elim]
                simp [PosNum.succ, trPosNum]
                omega
            exact
              ⟨Γ'.bit1 :: reversePrefix, [],
                some Γ'.cons, ⟨rfl⟩, first.trans second⟩
        | bit1 smaller induction =>
            intro reversePrefix
            let middle : Cfg' :=
              ⟨some (Λ'.pred q₁ q₂), some Γ'.bit0,
                K'.elim
                  (trPosNum smaller.succ ++
                    Γ'.cons :: trList tail)
                  (Γ'.bit1 :: reversePrefix) c d⟩
            have firstStep :
                TM2.step tr
                    ⟨some (Λ'.pred q₁ q₂), s,
                      K'.elim
                        (trPosNum (PosNum.bit1 smaller).succ ++
                          Γ'.cons :: trList tail)
                        reversePrefix c d⟩ =
                  some middle := by
              simp [middle, trPosNum, PosNum.succ,
                TM2.step, tr.eq_def]
              rfl
            have first :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  ((trPosNum (PosNum.bit1 smaller).succ).length +
                    1 + (trList tail).length +
                    reversePrefix.length + c.length + d.length)
                  ⟨some (Λ'.pred q₁ q₂), s,
                    K'.elim
                      (trPosNum (PosNum.bit1 smaller).succ ++
                        Γ'.cons :: trList tail)
                      reversePrefix c d⟩
                  middle := by
              apply EvalsToInSpace.single firstStep
              · rw [stackSpace_elim]
                simp [trPosNum, PosNum.succ]
                omega
              · rw [stackSpace_elim]
                simp [trPosNum, PosNum.succ]
                omega
            obtain ⟨finalReverse, finalMain, finalState,
              representation, rest⟩ :=
                induction (s := some Γ'.bit0)
                  (Γ'.bit1 :: reversePrefix)
            have rest' :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  ((trPosNum (PosNum.bit1 smaller).succ).length +
                    1 + (trList tail).length +
                    reversePrefix.length + c.length + d.length)
                  middle
                  ⟨some (unrev q₂), finalState,
                    K'.elim
                      (finalMain ++ Γ'.cons :: trList tail)
                      finalReverse c d⟩ := by
              simpa [middle, trPosNum, PosNum.succ,
                Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                using rest
            exact
              ⟨finalReverse, finalMain, finalState,
                representation, first.trans rest'⟩
        | bit0 smaller induction =>
            intro reversePrefix
            obtain ⟨headSymbol, remaining, encodingLift,
              notDelimiterLift⟩ :
                Σ headSymbol remaining,
                  PLift
                    (trPosNum smaller =
                      headSymbol :: remaining) ×
                  PLift (natEnd headSymbol = false) := by
              cases smaller <;>
                exact ⟨_, _, ⟨rfl⟩, ⟨rfl⟩⟩
            have encoding := encodingLift.down
            have notDelimiter := notDelimiterLift.down
            let afterPred : Cfg' :=
              ⟨some (unrev q₂), some headSymbol,
                K'.elim
                  (trPosNum smaller ++
                    Γ'.cons :: trList tail)
                  (Γ'.bit0 :: reversePrefix) c d⟩
            have predStep :
                TM2.step tr
                    ⟨some (Λ'.pred q₁ q₂), s,
                      K'.elim
                        (trPosNum (PosNum.bit0 smaller).succ ++
                          Γ'.cons :: trList tail)
                        reversePrefix c d⟩ =
                  some afterPred := by
              simp [afterPred, trPosNum, PosNum.succ,
                encoding, notDelimiter,
                show some Γ'.bit1 ≠ some Γ'.bit0 by decide,
                Option.getD, -natEnd, TM2.step, tr.eq_def]
              rfl
            have run :
                EvalsToInSpace (TM2.step tr) TM2.stackSpace
                  ((trPosNum (PosNum.bit0 smaller).succ).length +
                    1 + (trList tail).length +
                    reversePrefix.length + c.length + d.length)
                  ⟨some (Λ'.pred q₁ q₂), s,
                    K'.elim
                      (trPosNum (PosNum.bit0 smaller).succ ++
                        Γ'.cons :: trList tail)
                      reversePrefix c d⟩
                  afterPred := by
              apply EvalsToInSpace.single predStep
              · rw [stackSpace_elim]
                simp [trPosNum, PosNum.succ]
                omega
              · rw [stackSpace_elim]
                simp [trPosNum, PosNum.succ]
                omega
            exact
              ⟨Γ'.bit0 :: reversePrefix, trPosNum smaller,
                some headSymbol, ⟨rfl⟩, by
                  simpa [afterPred, trPosNum] using run⟩

/-- The data-space obligations needed to simulate one structurally
normalized `Code` call within a common low-level budget.  Recursive clauses
record precisely the normal call that Mathlib's `stepNormal` selects. -/
def normalSimulationFits :
    ToPartrec.Code → ToPartrec.Cont → List Nat → Nat → Prop
  | .zero', continuation, values, bound =>
      encodedListSpace values + continuationSpace continuation + 1 ≤
        bound
  | .succ, continuation, values, bound =>
      encodedListSpace values + continuationSpace continuation + 1 ≤
          bound ∧
        encodedListSpace [values.headI] +
            continuationSpace continuation + 1 ≤
          bound
  | .tail, continuation, values, bound =>
      encodedListSpace values + continuationSpace continuation ≤ bound
  | .cons first rest, continuation, values, bound =>
      normalSimulationFits first
        (.cons₁ rest values continuation) values bound
  | .comp first second, continuation, values, bound =>
      normalSimulationFits second (.comp first continuation) values bound
  | .case zeroBranch successorBranch, continuation, values, bound =>
      encodedListSpace values + continuationSpace continuation ≤ bound ∧
        values.headI.rec
          (normalSimulationFits zeroBranch continuation
            values.tail bound)
          (fun predecessor _ =>
            normalSimulationFits successorBranch continuation
              (predecessor :: values.tail) bound)
  | .fix body, continuation, values, bound =>
      normalSimulationFits body (.fix body continuation) values bound

/-- The least common budget described by `normalSimulationFits`. -/
def normalSimulationSpace :
    ToPartrec.Code → ToPartrec.Cont → List Nat → Nat
  | .zero', continuation, values =>
      encodedListSpace values + continuationSpace continuation + 1
  | .succ, continuation, values =>
      max
        (encodedListSpace values + continuationSpace continuation + 1)
        (encodedListSpace [values.headI] +
          continuationSpace continuation + 1)
  | .tail, continuation, values =>
      encodedListSpace values + continuationSpace continuation
  | .cons first rest, continuation, values =>
      normalSimulationSpace first
        (.cons₁ rest values continuation) values
  | .comp first second, continuation, values =>
      normalSimulationSpace second (.comp first continuation) values
  | .case zeroBranch successorBranch, continuation, values =>
      max
        (encodedListSpace values + continuationSpace continuation)
        (values.headI.rec
          (normalSimulationSpace zeroBranch continuation values.tail)
          (fun predecessor _ =>
            normalSimulationSpace successorBranch continuation
              (predecessor :: values.tail)))
  | .fix body, continuation, values =>
      normalSimulationSpace body (.fix body continuation) values

/-- The predicate form and numeric form of a normal-call space obligation
agree exactly. -/
theorem normalSimulationFits_iff
    (code : ToPartrec.Code) (continuation : ToPartrec.Cont)
    (values : List Nat) (bound : Nat) :
    normalSimulationFits code continuation values bound ↔
      normalSimulationSpace code continuation values ≤ bound := by
  induction code generalizing continuation values with
  | zero' =>
      simp [normalSimulationFits, normalSimulationSpace]
  | succ =>
      change
        (_ ≤ bound ∧ _ ≤ bound) ↔
          max
            (encodedListSpace values +
              continuationSpace continuation + 1)
            (encodedListSpace [values.headI] +
              continuationSpace continuation + 1) ≤
            bound
      constructor
      · intro inequalities
        exact max_le inequalities.1 inequalities.2
      · intro maximum
        exact
          ⟨(le_max_left _ _).trans maximum,
            (le_max_right _ _).trans maximum⟩
  | tail =>
      simp [normalSimulationFits, normalSimulationSpace]
  | cons first rest firstInduction _ =>
      exact firstInduction _ _
  | comp first second _ secondInduction =>
      exact secondInduction _ _
  | case zeroBranch successorBranch
      zeroInduction successorInduction =>
      cases head : values.headI with
      | zero =>
          simp [normalSimulationFits, normalSimulationSpace,
            head, zeroInduction]
      | succ predecessor =>
          simp [normalSimulationFits, normalSimulationSpace,
            head, successorInduction]
  | fix body induction =>
      exact induction _ _

/-- Every admissible normal-call budget bounds its initial evaluator
milestone. -/
theorem normalSimulationFits_start
    {code : ToPartrec.Code} {continuation : ToPartrec.Cont}
    {values : List Nat} {bound : Nat}
    (fits :
      normalSimulationFits code continuation values bound) :
    encodedListSpace values + continuationSpace continuation ≤ bound := by
  induction code generalizing continuation values with
  | zero' =>
      simp only [normalSimulationFits] at fits
      omega
  | succ =>
      simp only [normalSimulationFits] at fits
      omega
  | tail =>
      exact fits
  | cons first rest firstInduction _ =>
      simp only [normalSimulationFits] at fits
      have recursiveStart := firstInduction fits
      simp only [continuationSpace, trContStack, contStack,
        trLList, List.length_append, List.length_cons,
        encodedListSpace] at recursiveStart
      simp only [encodedListSpace, continuationSpace, trContStack]
      omega
  | comp first second _ secondInduction =>
      simp only [normalSimulationFits] at fits
      have recursiveStart := secondInduction fits
      simpa [continuationSpace, trContStack] using recursiveStart
  | case zeroBranch successorBranch zeroInduction successorInduction =>
      exact fits.1
  | fix body induction =>
      simp only [normalSimulationFits] at fits
      have recursiveStart := induction fits
      simpa [continuationSpace, trContStack] using recursiveStart

/-- A normal-call simulation certificate remains valid when its common
budget is enlarged. -/
theorem normalSimulationFits_mono
    {code : ToPartrec.Code} {continuation : ToPartrec.Cont}
    {values : List Nat} {small large : Nat}
    (fits : normalSimulationFits code continuation values small)
    (budget : small ≤ large) :
    normalSimulationFits code continuation values large := by
  induction code generalizing continuation values with
  | zero' =>
      simp only [normalSimulationFits] at fits ⊢
      omega
  | succ =>
      simp only [normalSimulationFits] at fits ⊢
      constructor <;> omega
  | tail =>
      exact fits.trans budget
  | cons first rest firstInduction _ =>
      exact firstInduction fits
  | comp first second _ secondInduction =>
      exact secondInduction fits
  | case zeroBranch successorBranch
      zeroInduction successorInduction =>
      simp only [normalSimulationFits] at fits ⊢
      refine ⟨fits.1.trans budget, ?_⟩
      cases head : values.headI with
      | zero =>
          apply zeroInduction
          simpa [head] using fits.2
      | succ predecessor =>
          apply successorInduction
          simpa [head] using fits.2
  | fix body induction =>
      exact induction fits

/-- Space-aware refinement of Mathlib's structurally normalized evaluator
call.  The supplied `normalSimulationFits` witness gives one common budget
for every primitive and recursive subcall in the normalization. -/
noncomputable def trNormal_respects_inSpace
    (code : ToPartrec.Code) (continuation : ToPartrec.Cont)
    (values : List Nat) (state : Option Γ') (bound : Nat)
    (fits :
      normalSimulationFits code continuation values bound) :
    Σ target,
      PLift
        (TrCfg (ToPartrec.stepNormal code continuation values) target) ×
      EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
        ⟨some (trNormal code (trCont continuation)), state,
          K'.elim (trList values) [] []
            (trContStack continuation)⟩
        target := by
  induction code generalizing continuation values state with
  | zero' =>
      simp only [normalSimulationFits] at fits
      simp only [encodedListSpace, continuationSpace] at fits
      let target : Cfg' :=
        ⟨some (Λ'.ret (trCont continuation)), state,
          K'.elim (Γ'.cons :: trList values) [] []
            (trContStack continuation)⟩
      have stepEq :
          TM2.step tr
              ⟨some
                  (trNormal ToPartrec.Code.zero'
                    (trCont continuation)),
                state,
                K'.elim (trList values) [] []
                  (trContStack continuation)⟩ =
            some target := by
        simp [target, TM2.step, tr.eq_def]
        rfl
      have startBound :
          TM2.stackSpace
              ⟨some
                  (trNormal ToPartrec.Code.zero'
                    (trCont continuation)),
                state,
                K'.elim (trList values) [] []
                  (trContStack continuation)⟩ ≤
            bound := by
        rw [stackSpace_elim]
        simp only [List.length_nil, add_zero]
        omega
      have targetBound :
          TM2.stackSpace target ≤ bound := by
        rw [stackSpace_elim]
        simp only [List.length_cons, List.length_nil, add_zero]
        omega
      exact
        ⟨target, ⟨⟨state, by
            simp [target]⟩⟩,
          EvalsToInSpace.single stepEq startBound targetBound⟩
  | succ =>
      simp only [normalSimulationFits] at fits
      have headRaw :=
        head_main_ok_inSpace
          (q :=
            Λ'.succ (Λ'.ret (trCont continuation)))
          (s := state) (L := values)
          (c := []) (d := trContStack continuation)
      have headBound :
          (trList values).length +
                (trContStack continuation).length + 1 ≤
            bound := by
        simpa [encodedListSpace, continuationSpace] using fits.1
      have head :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            ⟨some
                (head .main
                  (Λ'.succ
                    (Λ'.ret (trCont continuation)))),
              state,
              K'.elim (trList values) [] []
                (trContStack continuation)⟩
            ⟨some
                (Λ'.succ
                  (Λ'.ret (trCont continuation))),
              none,
              K'.elim (trList [values.headI]) [] []
                (trContStack continuation)⟩ :=
        headRaw.mono headBound
      have successorRaw :=
        succ_ok_inSpace
          (q := Λ'.ret (trCont continuation))
          (s := none) (n := values.headI)
          (c := []) (d := trContStack continuation)
      have successorBound :
          (trList [values.headI]).length +
                (trContStack continuation).length + 1 ≤
            bound := by
        simpa [encodedListSpace, continuationSpace] using fits.2
      have run := head.trans (successorRaw.mono successorBound)
      refine
        ⟨⟨some (Λ'.ret (trCont continuation)), none,
            K'.elim (trList [values.headI.succ]) [] []
              (trContStack continuation)⟩,
          ⟨⟨none, ?_⟩⟩, ?_⟩
      · simp
      · simpa [trNormal] using run
  | tail =>
      simp only [normalSimulationFits] at fits
      let delimiter : Option Γ' :=
        List.casesOn values none fun _ _ => some Γ'.cons
      have split :
          splitAtPred natEnd (trList values) =
            (trNat values.headI, delimiter,
              trList values.tail) := by
        apply splitAtPred_eq
        · exact trNat_natEnd _
        · cases values <;> simp [delimiter]
      have clearRaw :=
        clear_ok_inSpace
          (p := natEnd) (k := .main)
          (q := Λ'.ret (trCont continuation))
          (s := state)
          (tapeStacks :=
            K'.elim (trList values) [] []
              (trContStack continuation))
          split
      have startBound :
          TM2.stackSpace
              ⟨some
                  (trNormal ToPartrec.Code.tail
                    (trCont continuation)),
                state,
                K'.elim (trList values) [] []
                  (trContStack continuation)⟩ ≤
            bound := by
        rw [stackSpace_elim]
        simpa [encodedListSpace, continuationSpace] using fits
      let target : Cfg' :=
        ⟨some (Λ'.ret (trCont continuation)), delimiter,
          K'.elim (trList values.tail) [] []
            (trContStack continuation)⟩
      have run :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            ⟨some
                (trNormal ToPartrec.Code.tail
                  (trCont continuation)),
              state,
              K'.elim (trList values) [] []
                (trContStack continuation)⟩
            target := by
        convert clearRaw.mono startBound using 1
        all_goals simp [trNormal, target]
      exact
        ⟨target, ⟨⟨delimiter, by
            simp [target]⟩⟩, run⟩
  | cons first rest firstInduction restInduction =>
      simp only [normalSimulationFits] at fits
      have recursiveStart :=
        normalSimulationFits_start fits
      let recursiveContinuation : ToPartrec.Cont :=
        .cons₁ rest values continuation
      let recursiveLabel : Λ' :=
        trNormal first (trCont recursiveContinuation)
      let afterPush : Cfg' :=
        ⟨some
            (Λ'.move (fun _ => false) .main .rev
              (Λ'.copy recursiveLabel)),
          state,
          K'.elim (trList values) [] []
            (Γ'.consₗ :: trContStack continuation)⟩
      have pushStep :
          TM2.step tr
              ⟨some
                  (trNormal (.cons first rest)
                    (trCont continuation)),
                state,
                K'.elim (trList values) [] []
                  (trContStack continuation)⟩ =
            some afterPush := by
        simp [afterPush, recursiveLabel, recursiveContinuation,
          TM2.step, tr.eq_def]
        rfl
      have pushBound :
          TM2.stackSpace afterPush ≤ bound := by
        rw [stackSpace_elim]
        simp only [List.length_nil, List.length_cons, add_zero]
        simp only [continuationSpace,
          trContStack, contStack, trLList,
          List.length_append, List.length_cons,
          encodedListSpace] at recursiveStart
        simp only [trContStack]
        omega
      have startBound :
          TM2.stackSpace
              ⟨some
                  (trNormal (.cons first rest)
                    (trCont continuation)),
                state,
                K'.elim (trList values) [] []
                  (trContStack continuation)⟩ ≤
            bound := by
        rw [stackSpace_elim]
        simp only [List.length_nil, add_zero]
        simp only [continuationSpace,
          trContStack, contStack, trLList,
          List.length_append, List.length_cons,
          encodedListSpace] at recursiveStart
        simp only [trContStack]
        omega
      have push :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            ⟨some
                (trNormal (.cons first rest)
                  (trCont continuation)),
              state,
              K'.elim (trList values) [] []
                (trContStack continuation)⟩
            afterPush :=
        EvalsToInSpace.single pushStep startBound pushBound
      have moveRaw :=
        move_ok_inSpace
          (p := fun _ => false)
          (k₁ := .main) (k₂ := .rev)
          (q := Λ'.copy recursiveLabel)
          (s := state)
          (tapeStacks :=
            K'.elim (trList values) [] []
              (Γ'.consₗ :: trContStack continuation))
          (by decide) (splitAtPred_false _)
      let afterMove : Cfg' :=
        ⟨some (Λ'.copy recursiveLabel), none,
          K'.elim [] (trList values).reverse []
            (Γ'.consₗ :: trContStack continuation)⟩
      have move :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterPush afterMove := by
        convert moveRaw.mono pushBound using 1
        all_goals
          simp [afterMove, recursiveLabel, List.reverseAux_eq]
      have copyRaw :=
        copy_ok_inSpace recursiveLabel none []
          (trList values).reverse []
          (Γ'.consₗ :: trContStack continuation)
      let afterCopy : Cfg' :=
        ⟨some recursiveLabel, none,
          K'.elim (trList values) [] []
            (trList values ++
              Γ'.consₗ :: trContStack continuation)⟩
      have copyBudget :
          2 * (trList values).length +
                (trContStack continuation).length + 1 ≤
            bound := by
        simp only [continuationSpace,
          trContStack, contStack, trLList,
          List.length_append, List.length_cons,
          encodedListSpace] at recursiveStart
        simp only [trContStack]
        omega
      have copy :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterMove afterCopy := by
        have copyBudgetRaw :
            ([] : List Γ').length +
                  2 * (trList values).reverse.length +
                  ([] : List Γ').length +
                  (Γ'.consₗ ::
                    trContStack continuation).length ≤
                bound := by
          simp only [List.length_nil, zero_add,
            List.length_reverse, List.length_cons]
          omega
        convert copyRaw.mono copyBudgetRaw using 1
        all_goals
          simp [afterCopy, recursiveLabel, List.reverseAux_eq]
      obtain ⟨target, relatedLift, recursiveRun⟩ :=
        firstInduction recursiveContinuation values none fits
      have recursiveRun' :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterCopy target := by
        simpa [afterCopy, recursiveLabel,
          recursiveContinuation, trCont, trContStack,
          List.reverseAux_eq] using recursiveRun
      exact
        ⟨target, ⟨by
            simpa [ToPartrec.stepNormal,
              recursiveContinuation] using relatedLift.down⟩,
          ((push.trans move).trans copy).trans recursiveRun'⟩
  | comp first second firstInduction secondInduction =>
      simp only [normalSimulationFits] at fits
      obtain ⟨target, related, run⟩ :=
        secondInduction (.comp first continuation) values state fits
      exact
        ⟨target, ⟨by
            simpa [ToPartrec.stepNormal] using related.down⟩,
          by simpa [trNormal, trCont, trContStack] using run⟩
  | case zeroBranch successorBranch
      zeroInduction successorInduction =>
      simp only [normalSimulationFits] at fits
      obtain ⟨branchState, predecessorRaw⟩ :=
        pred_ok_inSpace
          (trNormal zeroBranch (trCont continuation))
          (trNormal successorBranch (trCont continuation))
          state values [] (trContStack continuation)
      have predecessor :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            ⟨some
                (trNormal
                  (.case zeroBranch successorBranch)
                  (trCont continuation)),
              state,
              K'.elim (trList values) [] []
                (trContStack continuation)⟩
            (values.headI.rec
              ⟨some
                  (trNormal zeroBranch
                    (trCont continuation)),
                branchState,
                K'.elim (trList values.tail) [] []
                  (trContStack continuation)⟩
              fun predecessor _ =>
                ⟨some
                    (trNormal successorBranch
                      (trCont continuation)),
                  branchState,
                  K'.elim
                    (trList (predecessor :: values.tail))
                    [] [] (trContStack continuation)⟩) := by
        have budget :
            (trList values).length +
                (trContStack continuation).length ≤ bound := by
          simpa [encodedListSpace, continuationSpace] using fits.1
        simpa [trNormal] using predecessorRaw.mono budget
      cases headValue : values.headI with
      | zero =>
          simp only [headValue, Nat.rec_zero] at fits predecessor
          obtain ⟨target, related, branchRun⟩ :=
            zeroInduction continuation values.tail branchState fits.2
          exact
            ⟨target, ⟨by
                simpa [ToPartrec.stepNormal, headValue] using
                  related.down⟩,
              predecessor.trans branchRun⟩
      | succ predecessorValue =>
          simp only [headValue] at fits predecessor
          obtain ⟨target, related, branchRun⟩ :=
            successorInduction continuation
              (predecessorValue :: values.tail)
              branchState fits.2
          exact
            ⟨target, ⟨by
                simpa [ToPartrec.stepNormal, headValue] using
                  related.down⟩,
              predecessor.trans branchRun⟩
  | fix body induction =>
      simp only [normalSimulationFits] at fits
      obtain ⟨target, related, run⟩ :=
        induction (.fix body continuation) values state fits
      exact
        ⟨target, ⟨by
            simpa [ToPartrec.stepNormal] using related.down⟩,
          by simpa [trNormal, trCont, trContStack] using run⟩

/-- The data-space obligations needed to execute one continuation return
within a common low-level budget. -/
def retSimulationFits :
    ToPartrec.Cont → List Nat → Nat → Prop
  | .halt, values, bound =>
      encodedListSpace values ≤ bound
  | .cons₁ rest arguments continuation, values, bound =>
      encodedListSpace values +
            continuationSpace (.cons₁ rest arguments continuation) ≤
          bound ∧
        normalSimulationFits rest (.cons₂ values continuation)
          arguments bound
  | .cons₂ saved continuation, values, bound =>
      encodedListSpace values +
            continuationSpace (.cons₂ saved continuation) ≤
          bound ∧
        retSimulationFits continuation (saved.headI :: values) bound
  | .comp first continuation, values, bound =>
      encodedListSpace values +
            continuationSpace (.comp first continuation) ≤
          bound ∧
        normalSimulationFits first continuation values bound
  | .fix body continuation, values, bound =>
      encodedListSpace values +
            continuationSpace (.fix body continuation) ≤
          bound ∧
        if values.headI = 0 then
          retSimulationFits continuation values.tail bound
        else
          normalSimulationFits body (.fix body continuation)
            values.tail bound

/-- The least common budget described by `retSimulationFits`. -/
def retSimulationSpace :
    ToPartrec.Cont → List Nat → Nat
  | .halt, values =>
      encodedListSpace values
  | .cons₁ rest arguments continuation, values =>
      max
        (encodedListSpace values +
          continuationSpace (.cons₁ rest arguments continuation))
        (normalSimulationSpace rest (.cons₂ values continuation)
          arguments)
  | .cons₂ saved continuation, values =>
      max
        (encodedListSpace values +
          continuationSpace (.cons₂ saved continuation))
        (retSimulationSpace continuation (saved.headI :: values))
  | .comp first continuation, values =>
      max
        (encodedListSpace values +
          continuationSpace (.comp first continuation))
        (normalSimulationSpace first continuation values)
  | .fix body continuation, values =>
      max
        (encodedListSpace values +
          continuationSpace (.fix body continuation))
        (if values.headI = 0 then
          retSimulationSpace continuation values.tail
        else
          normalSimulationSpace body (.fix body continuation)
            values.tail)

/-- The predicate form and numeric form of a continuation-return space
obligation agree exactly. -/
theorem retSimulationFits_iff
    (continuation : ToPartrec.Cont) (values : List Nat)
    (bound : Nat) :
    retSimulationFits continuation values bound ↔
      retSimulationSpace continuation values ≤ bound := by
  induction continuation generalizing values with
  | halt =>
      simp [retSimulationFits, retSimulationSpace]
  | cons₁ rest arguments continuation induction =>
      simp [retSimulationFits, retSimulationSpace,
        normalSimulationFits_iff]
  | cons₂ saved continuation induction =>
      simp [retSimulationFits, retSimulationSpace,
        induction]
  | comp first continuation induction =>
      simp [retSimulationFits, retSimulationSpace,
        normalSimulationFits_iff]
  | fix body continuation induction =>
      by_cases zero : values.headI = 0
      · simp [retSimulationFits, retSimulationSpace,
          zero, induction]
      · simp [retSimulationFits, retSimulationSpace,
          zero, normalSimulationFits_iff]

/-- Every admissible continuation-return budget bounds its initial evaluator
milestone. -/
theorem retSimulationFits_start
    {continuation : ToPartrec.Cont} {values : List Nat}
    {bound : Nat}
    (fits : retSimulationFits continuation values bound) :
    encodedListSpace values + continuationSpace continuation ≤ bound := by
  cases continuation <;>
    simp only [retSimulationFits] at fits
  · simpa [continuationSpace, trContStack] using fits
  all_goals exact fits.1

/-- A continuation-return simulation certificate remains valid when its
common budget is enlarged. -/
theorem retSimulationFits_mono
    {continuation : ToPartrec.Cont} {values : List Nat}
    {small large : Nat}
    (fits : retSimulationFits continuation values small)
    (budget : small ≤ large) :
    retSimulationFits continuation values large := by
  induction continuation generalizing values with
  | halt =>
      exact fits.trans budget
  | cons₁ rest arguments continuation induction =>
      simp only [retSimulationFits] at fits ⊢
      exact
        ⟨fits.1.trans budget,
          normalSimulationFits_mono fits.2 budget⟩
  | cons₂ saved continuation induction =>
      simp only [retSimulationFits] at fits ⊢
      exact ⟨fits.1.trans budget, induction fits.2⟩
  | comp first continuation induction =>
      simp only [retSimulationFits] at fits ⊢
      exact
        ⟨fits.1.trans budget,
          normalSimulationFits_mono fits.2 budget⟩
  | fix body continuation induction =>
      simp only [retSimulationFits] at fits ⊢
      refine ⟨fits.1.trans budget, ?_⟩
      split <;> rename_i branch
      · exact induction (by simpa [branch] using fits.2)
      · exact
          normalSimulationFits_mono
            (by simpa [branch] using fits.2) budget

/-- Space-aware refinement of one continuation return. -/
noncomputable def tr_ret_respects_inSpace
    (continuation : ToPartrec.Cont) (values : List Nat)
    (state : Option Γ') (bound : Nat)
    (fits : retSimulationFits continuation values bound) :
    Σ target,
      PLift (TrCfg (ToPartrec.stepRet continuation values) target) ×
      EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
        ⟨some (Λ'.ret (trCont continuation)), state,
          K'.elim (trList values) [] []
            (trContStack continuation)⟩
        target := by
  induction continuation generalizing values state with
  | halt =>
      simp only [retSimulationFits] at fits
      let target := halt values
      have stepEq :
          TM2.step tr
              ⟨some (Λ'.ret (trCont ToPartrec.Cont.halt)),
                state,
                K'.elim (trList values) [] [] []⟩ =
            some target := by
        simp [target, halt, TM2.step, tr.eq_def]
        rfl
      have startBound :
          TM2.stackSpace
              ⟨some (Λ'.ret (trCont ToPartrec.Cont.halt)),
                state,
                K'.elim (trList values) [] [] []⟩ ≤
            bound := by
        rw [stackSpace_elim]
        simpa [encodedListSpace] using fits
      have targetBound :
          TM2.stackSpace target ≤ bound := by
        simpa [target] using fits
      exact
        ⟨target, ⟨by exact rfl⟩,
          EvalsToInSpace.single stepEq startBound targetBound⟩
  | cons₁ rest arguments continuation induction =>
      simp only [retSimulationFits] at fits
      let recursiveContinuation : ToPartrec.Cont :=
        .cons₂ values continuation
      let recursiveLabel : Λ' :=
        trNormal rest (trCont recursiveContinuation)
      let thirdMove : Λ' :=
        move₂ (fun _ => false) .aux .stack recursiveLabel
      let secondMove : Λ' :=
        move₂ (fun symbol => symbol = Γ'.consₗ)
          .stack .main thirdMove
      let firstMove : Λ' :=
        move₂ (fun _ => false) .main .aux secondMove
      let afterGoto : Cfg' :=
        ⟨some firstMove, state,
          K'.elim (trList values) [] []
            (trList arguments ++
              Γ'.consₗ :: trContStack continuation)⟩
      have gotoStep :
          TM2.step tr
              ⟨some
                  (Λ'.ret
                    (trCont
                      (.cons₁ rest arguments continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack
                    (.cons₁ rest arguments continuation))⟩ =
            some afterGoto := by
        simp [afterGoto, firstMove, secondMove, thirdMove,
          recursiveLabel, recursiveContinuation,
          trCont, trContStack, TM2.step, tr.eq_def]
        rfl
      have sourceBound :
          TM2.stackSpace
              ⟨some
                  (Λ'.ret
                    (trCont
                      (.cons₁ rest arguments continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack
                    (.cons₁ rest arguments continuation))⟩ ≤
            bound := by
        rw [stackSpace_elim]
        simpa [encodedListSpace, continuationSpace] using fits.1
      have gotoBound :
          TM2.stackSpace afterGoto ≤ bound := by
        rw [stackSpace_elim]
        simpa [afterGoto, encodedListSpace, continuationSpace,
          trContStack, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using fits.1
      have goto :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            ⟨some
                (Λ'.ret
                  (trCont
                    (.cons₁ rest arguments continuation))),
              state,
              K'.elim (trList values) [] []
                (trContStack
                  (.cons₁ rest arguments continuation))⟩
            afterGoto :=
        EvalsToInSpace.single gotoStep sourceBound gotoBound
      have firstRaw :=
        move₂_ok_inSpace
          (p := fun _ => false)
          (k₁ := .main) (k₂ := .aux)
          (q := secondMove) (s := state)
          (tapeStacks :=
            K'.elim (trList values) [] []
              (trList arguments ++
                Γ'.consₗ :: trContStack continuation))
          (by decide) rfl (splitAtPred_false _)
      let afterFirst : Cfg' :=
        ⟨some secondMove, none,
          K'.elim [] [] (trList values)
            (trList arguments ++
              Γ'.consₗ :: trContStack continuation)⟩
      have firstMoveRun :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterGoto afterFirst := by
        convert firstRaw.mono gotoBound using 1
        all_goals
          simp [afterFirst, secondMove]
      have stackSplit :
          splitAtPred
              (fun symbol => symbol = Γ'.consₗ)
              (trList arguments ++
                Γ'.consₗ :: trContStack continuation) =
            (trList arguments, some Γ'.consₗ,
              trContStack continuation) := by
        apply splitAtPred_eq
        · exact fun symbol member =>
            Bool.decide_false
              (trList_ne_consₗ _ _ member)
        · exact ⟨rfl, by simp⟩
      have secondRaw :=
        move₂_ok_inSpace
          (p := fun symbol => symbol = Γ'.consₗ)
          (k₁ := .stack) (k₂ := .main)
          (q := thirdMove) (s := none)
          (tapeStacks :=
            K'.elim [] [] (trList values)
              (trList arguments ++
                Γ'.consₗ :: trContStack continuation))
          (by decide) rfl stackSplit
      let afterSecond : Cfg' :=
        ⟨some thirdMove, none,
          K'.elim (trList arguments) []
            (trList values)
            (Γ'.consₗ :: trContStack continuation)⟩
      have secondMoveRun :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterFirst afterSecond := by
        convert secondRaw.mono firstMoveRun.last_le using 1
        all_goals
          simp [afterSecond, thirdMove]
      have thirdRaw :=
        move₂_ok_inSpace
          (p := fun _ => false)
          (k₁ := .aux) (k₂ := .stack)
          (q := recursiveLabel) (s := none)
          (tapeStacks :=
            K'.elim (trList arguments) []
              (trList values)
              (Γ'.consₗ :: trContStack continuation))
          (by decide) rfl (splitAtPred_false _)
      let afterThird : Cfg' :=
        ⟨some recursiveLabel, none,
          K'.elim (trList arguments) [] []
            (trList values ++
              Γ'.consₗ :: trContStack continuation)⟩
      have thirdMoveRun :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterSecond afterThird := by
        convert thirdRaw.mono secondMoveRun.last_le using 1
        all_goals
          simp [afterThird, recursiveLabel]
      obtain ⟨target, related, recursiveRun⟩ :=
        trNormal_respects_inSpace rest recursiveContinuation
          arguments none bound fits.2
      have recursiveRun' :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterThird target := by
        simpa [afterThird, recursiveLabel,
          recursiveContinuation, trContStack] using recursiveRun
      exact
        ⟨target, ⟨by
            simpa [ToPartrec.stepRet,
              recursiveContinuation] using related.down⟩,
          (((goto.trans firstMoveRun).trans secondMoveRun).trans
            thirdMoveRun).trans recursiveRun'⟩
  | cons₂ saved continuation induction =>
      simp only [retSimulationFits] at fits
      let afterGoto : Cfg' :=
        ⟨some
            (head .stack
              (Λ'.ret (trCont continuation))),
          state,
          K'.elim (trList values) [] []
            (trList saved ++
              Γ'.consₗ :: trContStack continuation)⟩
      have gotoStep :
          TM2.step tr
              ⟨some
                  (Λ'.ret
                    (trCont (.cons₂ saved continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack
                    (.cons₂ saved continuation))⟩ =
            some afterGoto := by
        simp [afterGoto, trCont, trContStack,
          TM2.step, tr.eq_def]
        rfl
      have sourceBound :
          TM2.stackSpace
              ⟨some
                  (Λ'.ret
                    (trCont (.cons₂ saved continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack
                    (.cons₂ saved continuation))⟩ ≤
            bound := by
        rw [stackSpace_elim]
        simpa [encodedListSpace, continuationSpace] using fits.1
      have gotoBound :
          TM2.stackSpace afterGoto ≤ bound := by
        rw [stackSpace_elim]
        simpa [afterGoto, encodedListSpace, continuationSpace,
          trContStack, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using fits.1
      have goto :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            ⟨some
                (Λ'.ret
                  (trCont (.cons₂ saved continuation))),
              state,
              K'.elim (trList values) [] []
                (trContStack
                  (.cons₂ saved continuation))⟩
            afterGoto :=
        EvalsToInSpace.single gotoStep sourceBound gotoBound
      have headRaw :=
        head_stack_ok_inSpace
          (q := Λ'.ret (trCont continuation))
          (s := state) (L₁ := values)
          (L₂ := saved) (L₃ := trContStack continuation)
      have headBudget :
          (trList values).length + (trList saved).length +
                (trContStack continuation).length + 1 ≤
            bound := by
        simpa [encodedListSpace, continuationSpace,
          trContStack, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using fits.1
      have headRun :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterGoto
            ⟨some (Λ'.ret (trCont continuation)), none,
              K'.elim (trList (saved.headI :: values)) [] []
                (trContStack continuation)⟩ := by
        simpa [afterGoto] using headRaw.mono headBudget
      obtain ⟨target, related, recursiveRun⟩ :=
        induction (saved.headI :: values) none fits.2
      exact
        ⟨target, ⟨by
            simpa [ToPartrec.stepRet] using related.down⟩,
          (goto.trans headRun).trans recursiveRun⟩
  | comp first continuation induction =>
      simp only [retSimulationFits] at fits
      let afterGoto : Cfg' :=
        ⟨some (trNormal first (trCont continuation)), state,
          K'.elim (trList values) [] []
            (trContStack continuation)⟩
      have gotoStep :
          TM2.step tr
              ⟨some
                  (Λ'.ret
                    (trCont (.comp first continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack (.comp first continuation))⟩ =
            some afterGoto := by
        simp [afterGoto, trCont, trContStack,
          TM2.step, tr.eq_def]
        rfl
      have sourceBound :
          TM2.stackSpace
              ⟨some
                  (Λ'.ret
                    (trCont (.comp first continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack (.comp first continuation))⟩ ≤
            bound := by
        rw [stackSpace_elim]
        simpa [encodedListSpace, continuationSpace] using fits.1
      have gotoBound :
          TM2.stackSpace afterGoto ≤ bound := by
        rw [stackSpace_elim]
        simpa [afterGoto, encodedListSpace, continuationSpace,
          trContStack] using fits.1
      have goto :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            ⟨some
                (Λ'.ret
                  (trCont (.comp first continuation))),
              state,
              K'.elim (trList values) [] []
                (trContStack (.comp first continuation))⟩
            afterGoto :=
        EvalsToInSpace.single gotoStep sourceBound gotoBound
      obtain ⟨target, related, normalRun⟩ :=
        trNormal_respects_inSpace first continuation values
          state bound fits.2
      have normalRun' :
          EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            afterGoto target := by
        simpa [afterGoto] using normalRun
      exact
        ⟨target, ⟨by
            simpa [ToPartrec.stepRet] using related.down⟩,
          goto.trans normalRun'⟩
  | fix body continuation induction =>
      simp only [retSimulationFits] at fits
      have encodedHead :
          if values.headI = 0 then
            natEnd ((trList values).head?.getD default) = true ∧
              (trList values).tail = trList values.tail
          else
            natEnd ((trList values).head?.getD default) = false ∧
              (trList values).tail =
                (trNat values.headI).tail ++
                  Γ'.cons :: trList values.tail := by
        obtain - | value := values
        · exact ⟨rfl, rfl⟩
        rcases value with - | value
        · simp
        rw [trList, List.headI, trNat, Nat.cast_succ,
          Num.add_one, Num.succ, List.tail]
        cases (value : Num).succ' <;> exact ⟨rfl, rfl⟩
      by_cases isZero : values.headI = 0
      · simp only [isZero, if_pos] at fits encodedHead
        let afterPop : Cfg' :=
          ⟨some (Λ'.ret (trCont continuation)),
            (trList values).head?,
            K'.elim (trList values.tail) [] []
              (trContStack continuation)⟩
        have popStep :
            TM2.step tr
                ⟨some
                    (Λ'.ret
                      (trCont (.fix body continuation))),
                  state,
                  K'.elim (trList values) [] []
                    (trContStack
                      (.fix body continuation))⟩ =
              some afterPop := by
          change
            some
                (TM2.stepAux
                  (tr
                    (Λ'.ret
                      (Cont'.fix body
                        (trCont continuation))))
                  state
                  (K'.elim (trList values) [] []
                    (trContStack
                      (.fix body continuation)))) =
              some afterPop
          rw [tr_ret_fix]
          simp only [pop', TM2.stepAux, K'.elim_main,
            encodedHead.1, K'.elim_update_main]
          simp [afterPop, trContStack, encodedHead.2]
          rfl
        have sourceBound :
            TM2.stackSpace
                ⟨some
                    (Λ'.ret
                      (trCont (.fix body continuation))),
                  state,
                  K'.elim (trList values) [] []
                    (trContStack
                      (.fix body continuation))⟩ ≤
              bound := by
          rw [stackSpace_elim]
          simpa [encodedListSpace, continuationSpace] using fits.1
        have popBound :
            TM2.stackSpace afterPop ≤ bound := by
          rw [stackSpace_elim]
          rw [stackSpace_elim] at sourceBound
          have tailLength :
              (trList values.tail).length ≤
                (trList values).length := by
            rw [← encodedHead.2]
            cases trList values <;> simp
          simp only [List.length_nil, add_zero,
            trContStack, contStack] at sourceBound ⊢
          omega
        have pop :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
              ⟨some
                  (Λ'.ret
                    (trCont (.fix body continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack
                    (.fix body continuation))⟩
              afterPop :=
          EvalsToInSpace.single popStep sourceBound popBound
        obtain ⟨target, related, recursiveRun⟩ :=
          induction values.tail (trList values).head? fits.2
        have recursiveRun' :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
              afterPop target := by
          simpa [afterPop] using recursiveRun
        exact
          ⟨target, ⟨by
              simpa [ToPartrec.stepRet, isZero] using
                related.down⟩,
            pop.trans recursiveRun'⟩
      · simp only [isZero, if_false] at fits encodedHead
        let recursiveContinuation : ToPartrec.Cont :=
          .fix body continuation
        let recursiveLabel : Λ' :=
          trNormal body (trCont recursiveContinuation)
        let afterPop : Cfg' :=
          ⟨some
              (Λ'.clear natEnd .main recursiveLabel),
            (trList values).head?,
            K'.elim (trList values).tail [] []
              (trContStack continuation)⟩
        have popStep :
            TM2.step tr
                ⟨some
                    (Λ'.ret
                      (trCont
                        (.fix body continuation))),
                  state,
                  K'.elim (trList values) [] []
                    (trContStack
                      (.fix body continuation))⟩ =
              some afterPop := by
          change
            some
                (TM2.stepAux
                  (tr
                    (Λ'.ret
                      (Cont'.fix body
                        (trCont continuation))))
                  state
                  (K'.elim (trList values) [] []
                    (trContStack
                      (.fix body continuation)))) =
              some afterPop
          rw [tr_ret_fix]
          simp only [pop', TM2.stepAux, K'.elim_main,
            encodedHead.1, K'.elim_update_main]
          simp [afterPop, recursiveLabel,
            recursiveContinuation, trCont, trContStack]
          rfl
        have sourceBound :
            TM2.stackSpace
                ⟨some
                    (Λ'.ret
                      (trCont
                        (.fix body continuation))),
                  state,
                  K'.elim (trList values) [] []
                    (trContStack
                      (.fix body continuation))⟩ ≤
              bound := by
          rw [stackSpace_elim]
          simpa [encodedListSpace, continuationSpace] using fits.1
        have popBound :
            TM2.stackSpace afterPop ≤ bound := by
          rw [stackSpace_elim]
          rw [stackSpace_elim] at sourceBound
          have tailLength :
              (trList values).tail.length ≤
                (trList values).length := by
            cases trList values <;> simp
          simp only [List.length_nil, add_zero,
            trContStack, contStack] at sourceBound ⊢
          omega
        have pop :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
              ⟨some
                  (Λ'.ret
                    (trCont
                      (.fix body continuation))),
                state,
                K'.elim (trList values) [] []
                  (trContStack
                    (.fix body continuation))⟩
              afterPop :=
          EvalsToInSpace.single popStep sourceBound popBound
        have split :
            splitAtPred natEnd (trList values).tail =
              ((trNat values.headI).tail, some Γ'.cons,
                trList values.tail) := by
          apply splitAtPred_eq
          · exact fun symbol member =>
              trNat_natEnd _ _
                (List.tail_subset _ member)
          · exact ⟨rfl, encodedHead.2⟩
        have clearRaw :=
          clear_ok_inSpace
            (p := natEnd) (k := .main)
            (q := recursiveLabel)
            (s := (trList values).head?)
            (tapeStacks :=
              K'.elim (trList values).tail [] []
                (trContStack continuation))
            split
        let afterClear : Cfg' :=
          ⟨some recursiveLabel, some Γ'.cons,
            K'.elim (trList values.tail) [] []
              (trContStack continuation)⟩
        have clear :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
              afterPop afterClear := by
          convert clearRaw.mono pop.last_le using 1
          all_goals
            simp [afterClear, recursiveLabel]
        obtain ⟨target, related, normalRun⟩ :=
          trNormal_respects_inSpace body recursiveContinuation
            values.tail (some Γ'.cons) bound fits.2
        have normalRun' :
            EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
              afterClear target := by
          simpa [afterClear, recursiveLabel,
            recursiveContinuation, trContStack] using normalRun
        exact
          ⟨target, ⟨by
              simpa [ToPartrec.stepRet, isZero,
                recursiveContinuation] using related.down⟩,
            (pop.trans clear).trans normalRun'⟩

/-- The data-space obligation attached to a high-level evaluator
configuration. -/
def cfgSimulationFits :
    ToPartrec.Cfg → Nat → Prop
  | .halt values, bound =>
      encodedListSpace values ≤ bound
  | .ret continuation values, bound =>
      retSimulationFits continuation values bound

/-- The least common budget needed to simulate one high-level evaluator
configuration. -/
def cfgSimulationSpace : ToPartrec.Cfg → Nat
  | .halt values =>
      encodedListSpace values
  | .ret continuation values =>
      retSimulationSpace continuation values

/-- The predicate form and numeric form of a configuration space obligation
agree exactly. -/
theorem cfgSimulationFits_iff
    (configuration : ToPartrec.Cfg) (bound : Nat) :
    cfgSimulationFits configuration bound ↔
      cfgSimulationSpace configuration ≤ bound := by
  cases configuration with
  | halt values =>
      simp [cfgSimulationFits, cfgSimulationSpace]
  | ret continuation values =>
      simp [cfgSimulationFits, cfgSimulationSpace,
        retSimulationFits_iff]

/-- A finite evaluator execution whose every return (and final halt) has a
numeric simulation requirement within `bound`.  This continuation-passing
certificate is convenient for composing nested program calls backward from
their final result. -/
inductive EvaluatorExecutionFits (bound : Nat) :
    ToPartrec.Cfg → Prop
  | halt (values : List Nat)
      (space : encodedListSpace values ≤ bound) :
      EvaluatorExecutionFits bound (.halt values)
  | ret (continuation : ToPartrec.Cont) (values : List Nat)
      (space : retSimulationSpace continuation values ≤ bound)
      (next :
      EvaluatorExecutionFits bound
          (ToPartrec.stepRet continuation values)) :
      EvaluatorExecutionFits bound (.ret continuation values)

/-- A structurally normalized code call followed by a finite fitted
continuation execution. -/
structure EvaluatorCallFits
    (code : ToPartrec.Code) (continuation : ToPartrec.Cont)
    (values : List Nat) (bound : Nat) : Prop where
  normal :
    normalSimulationSpace code continuation values ≤ bound
  execution :
    EvaluatorExecutionFits bound
      (ToPartrec.stepNormal code continuation values)

namespace EvaluatorExecutionFits

/-- The current configuration of a finite fitted execution satisfies its
numeric simulation requirement. -/
theorem current_space
    {bound : Nat} {configuration : ToPartrec.Cfg}
    (execution : EvaluatorExecutionFits bound configuration) :
    cfgSimulationSpace configuration ≤ bound := by
  cases execution with
  | halt values space =>
      exact space
  | ret continuation values space next =>
      exact space

/-- Advance a fitted execution by one high-level evaluator step. -/
theorem next
    {bound : Nat} {first next : ToPartrec.Cfg}
    (execution : EvaluatorExecutionFits bound first)
    (step : ToPartrec.step first = some next) :
    EvaluatorExecutionFits bound next := by
  cases execution with
  | halt values space =>
      simp [ToPartrec.step] at step
  | ret continuation values space after =>
      simp only [ToPartrec.step, Option.some.injEq] at step
      subst next
      exact after

/-- Advance a fitted execution along any finite high-level reachability
derivation. -/
theorem after_reaches
    {bound : Nat} {first last : ToPartrec.Cfg}
    (execution : EvaluatorExecutionFits bound first)
    (reachable : Reaches ToPartrec.step first last) :
    EvaluatorExecutionFits bound last := by
  induction reachable with
  | refl =>
      exact execution
  | @tail before after reachable edge induction =>
      apply induction.next
      simpa only [Option.mem_def] using edge

/-- Every high-level configuration reached along a fitted finite execution
satisfies its numeric simulation requirement. -/
theorem space_of_reaches
    {bound : Nat} {first last : ToPartrec.Cfg}
    (execution : EvaluatorExecutionFits bound first)
    (reachable : Reaches ToPartrec.step first last) :
    cfgSimulationSpace last ≤ bound :=
  (execution.after_reaches reachable).current_space

/-- Enlarge the common budget of a fitted finite execution. -/
theorem mono
    {small large : Nat} {configuration : ToPartrec.Cfg}
    (execution : EvaluatorExecutionFits small configuration)
    (budget : small ≤ large) :
    EvaluatorExecutionFits large configuration := by
  induction execution with
  | halt values space =>
      exact .halt values (space.trans budget)
  | ret continuation values space next induction =>
      exact .ret continuation values (space.trans budget) induction

/-- Finish a return to the halting continuation. -/
theorem ret_halt
    {values : List Nat} {bound : Nat}
    (space : encodedListSpace values ≤ bound) :
    EvaluatorExecutionFits bound
      (.ret ToPartrec.Cont.halt values) := by
  apply EvaluatorExecutionFits.ret ToPartrec.Cont.halt values
  · simpa [retSimulationSpace] using space
  · simpa [ToPartrec.stepRet] using
      EvaluatorExecutionFits.halt values space

/-- Return from the first half of `cons` into the call of its second
half. -/
theorem ret_cons₁
    {rest : ToPartrec.Code} {arguments values : List Nat}
    {continuation : ToPartrec.Cont} {bound : Nat}
    (source :
      encodedListSpace values +
          continuationSpace
            (.cons₁ rest arguments continuation) ≤
        bound)
    (call :
      EvaluatorCallFits rest (.cons₂ values continuation)
        arguments bound) :
    EvaluatorExecutionFits bound
      (.ret (.cons₁ rest arguments continuation) values) := by
  apply EvaluatorExecutionFits.ret
    (.cons₁ rest arguments continuation) values
  · simp only [retSimulationSpace]
    exact max_le source call.normal
  · simpa [ToPartrec.stepRet] using call.execution

/-- Return from the second half of `cons` into the enclosing
continuation. -/
theorem ret_cons₂
    {saved values : List Nat} {continuation : ToPartrec.Cont}
    {bound : Nat}
    (source :
      encodedListSpace values +
          continuationSpace (.cons₂ saved continuation) ≤
        bound)
    (after :
      EvaluatorExecutionFits bound
        (.ret continuation (saved.headI :: values))) :
    EvaluatorExecutionFits bound
      (.ret (.cons₂ saved continuation) values) := by
  have afterSpace :
      retSimulationSpace continuation (saved.headI :: values) ≤
        bound := by
    simpa [cfgSimulationSpace] using after.current_space
  apply EvaluatorExecutionFits.ret (.cons₂ saved continuation) values
  · simp only [retSimulationSpace]
    exact max_le source afterSpace
  · have nextAfter :=
      after.next
        (show ToPartrec.step
            (.ret continuation (saved.headI :: values)) =
              some (ToPartrec.stepRet continuation
                (saved.headI :: values)) by
          rfl)
    simpa [ToPartrec.stepRet] using nextAfter

/-- Return from the argument of a composition into its outer call. -/
theorem ret_comp
    {first : ToPartrec.Code} {values : List Nat}
    {continuation : ToPartrec.Cont} {bound : Nat}
    (source :
      encodedListSpace values +
          continuationSpace (.comp first continuation) ≤
        bound)
    (call :
      EvaluatorCallFits first continuation values bound) :
    EvaluatorExecutionFits bound
      (.ret (.comp first continuation) values) := by
  apply EvaluatorExecutionFits.ret (.comp first continuation) values
  · simp only [retSimulationSpace]
    exact max_le source call.normal
  · simpa [ToPartrec.stepRet] using call.execution

/-- Take the terminating branch of a fixed-point return. -/
theorem ret_fix_zero
    {body : ToPartrec.Code} {values : List Nat}
    {continuation : ToPartrec.Cont} {bound : Nat}
    (zero : values.headI = 0)
    (source :
      encodedListSpace values +
          continuationSpace (.fix body continuation) ≤
        bound)
    (after :
      EvaluatorExecutionFits bound
        (.ret continuation values.tail)) :
    EvaluatorExecutionFits bound
      (.ret (.fix body continuation) values) := by
  have afterSpace :
      retSimulationSpace continuation values.tail ≤ bound := by
    simpa [cfgSimulationSpace] using after.current_space
  apply EvaluatorExecutionFits.ret (.fix body continuation) values
  · simp [retSimulationSpace, zero]
    exact ⟨source, afterSpace⟩
  · have nextAfter :=
      after.next
        (show ToPartrec.step (.ret continuation values.tail) =
            some (ToPartrec.stepRet continuation values.tail) by
          rfl)
    simpa [ToPartrec.stepRet, zero] using nextAfter

/-- Take the recursive branch of a fixed-point return. -/
theorem ret_fix_succ
    {body : ToPartrec.Code} {values : List Nat}
    {continuation : ToPartrec.Cont} {bound : Nat}
    (nonzero : values.headI ≠ 0)
    (source :
      encodedListSpace values +
          continuationSpace (.fix body continuation) ≤
        bound)
    (call :
      EvaluatorCallFits body (.fix body continuation)
        values.tail bound) :
    EvaluatorExecutionFits bound
      (.ret (.fix body continuation) values) := by
  apply EvaluatorExecutionFits.ret (.fix body continuation) values
  · simp [retSimulationSpace, nonzero]
    exact ⟨source, call.normal⟩
  · simpa [ToPartrec.stepRet, nonzero] using call.execution

end EvaluatorExecutionFits

namespace EvaluatorCallFits

/-- A primitive or otherwise already-normalized call is fitted once its
normalization requirement and following execution are fitted. -/
theorem normalized
    {code : ToPartrec.Code} {continuation : ToPartrec.Cont}
    {values : List Nat} {bound : Nat}
    (normal :
      normalSimulationSpace code continuation values ≤ bound)
    (execution :
      EvaluatorExecutionFits bound
        (ToPartrec.stepNormal code continuation values)) :
    EvaluatorCallFits code continuation values bound :=
  ⟨normal, execution⟩

/-- Fit the `zero'` primitive.  Its one extra normalization cell is exactly
the delimiter of the zero prepended to the returned list. -/
theorem zero'
    {continuation : ToPartrec.Cont} {values : List Nat}
    {bound : Nat}
    (after :
      EvaluatorExecutionFits bound
        (.ret continuation (0 :: values))) :
    EvaluatorCallFits ToPartrec.Code.zero' continuation values
      bound := by
  have returnedSpace :
      evaluatorCfgSpace (.ret continuation (0 :: values)) ≤
        bound := by
    have returnedFits :
        retSimulationFits continuation (0 :: values) bound :=
      (retSimulationFits_iff _ _ _).2 (by
        simpa [cfgSimulationSpace] using after.current_space)
    simpa [evaluatorCfgSpace] using
      retSimulationFits_start returnedFits
  constructor
  · simp only [normalSimulationSpace]
    simp [evaluatorCfgSpace, encodedListSpace_cons,
      Computability.encodeNat, Computability.encodeNum] at returnedSpace
    omega
  · simpa [ToPartrec.stepNormal] using after

/-- Fit the binary-successor primitive from bounds on its source footprint
and its one-cell transient output overhead. -/
theorem succ
    {continuation : ToPartrec.Cont} {values : List Nat}
    {bound : Nat}
    (source :
      encodedListSpace values + continuationSpace continuation + 1 ≤
        bound)
    (result :
      encodedListSpace [values.headI] +
          continuationSpace continuation + 1 ≤
        bound)
    (after :
      EvaluatorExecutionFits bound
        (.ret continuation [values.headI.succ])) :
    EvaluatorCallFits ToPartrec.Code.succ continuation values
      bound := by
  constructor
  · simp only [normalSimulationSpace]
    exact max_le source result
  · simpa [ToPartrec.stepNormal] using after

/-- Fit the list-tail primitive from its source milestone bound. -/
theorem tail
    {continuation : ToPartrec.Cont} {values : List Nat}
    {bound : Nat}
    (source :
      encodedListSpace values + continuationSpace continuation ≤
        bound)
    (after :
      EvaluatorExecutionFits bound
        (.ret continuation values.tail)) :
    EvaluatorCallFits ToPartrec.Code.tail continuation values
      bound := by
  constructor
  · simpa [normalSimulationSpace] using source
  · simpa [ToPartrec.stepNormal] using after

/-- Fitting the selected first subcall fits normalization of `cons`. -/
theorem cons
    {first rest : ToPartrec.Code} {continuation : ToPartrec.Cont}
    {values : List Nat} {bound : Nat}
    (call :
      EvaluatorCallFits first
        (.cons₁ rest values continuation) values bound) :
    EvaluatorCallFits (.cons first rest) continuation values bound := by
  exact
    ⟨by simpa [normalSimulationSpace] using call.normal,
      by simpa [ToPartrec.stepNormal] using call.execution⟩

/-- Fitting the inner subcall fits normalization of a composition. -/
theorem comp
    {first second : ToPartrec.Code}
    {continuation : ToPartrec.Cont}
    {values : List Nat} {bound : Nat}
    (call :
      EvaluatorCallFits second (.comp first continuation)
        values bound) :
    EvaluatorCallFits (.comp first second) continuation values bound := by
  exact
    ⟨by simpa [normalSimulationSpace] using call.normal,
      by simpa [ToPartrec.stepNormal] using call.execution⟩

/-- Fit the zero branch selected during `case` normalization. -/
theorem case_zero
    {zeroBranch successorBranch : ToPartrec.Code}
    {continuation : ToPartrec.Cont}
    {values : List Nat} {bound : Nat}
    (zero : values.headI = 0)
    (source :
      encodedListSpace values + continuationSpace continuation ≤
        bound)
    (call :
      EvaluatorCallFits zeroBranch continuation values.tail bound) :
    EvaluatorCallFits (.case zeroBranch successorBranch)
      continuation values bound := by
  constructor
  · simp [normalSimulationSpace, zero]
    exact ⟨source, call.normal⟩
  · simpa [ToPartrec.stepNormal, zero] using call.execution

/-- Fit the successor branch selected during `case` normalization. -/
theorem case_succ
    {zeroBranch successorBranch : ToPartrec.Code}
    {continuation : ToPartrec.Cont}
    {values : List Nat} {bound : Nat}
    (predecessor : Nat)
    (head : values.headI = predecessor + 1)
    (source :
      encodedListSpace values + continuationSpace continuation ≤
        bound)
    (call :
      EvaluatorCallFits successorBranch continuation
        (predecessor :: values.tail) bound) :
    EvaluatorCallFits (.case zeroBranch successorBranch)
      continuation values bound := by
  constructor
  · simp [normalSimulationSpace, head]
    exact ⟨source, call.normal⟩
  · simpa [ToPartrec.stepNormal, head] using call.execution

/-- Fitting the body call fits normalization of `fix`. -/
theorem fix
    {body : ToPartrec.Code} {continuation : ToPartrec.Cont}
    {values : List Nat} {bound : Nat}
    (call :
      EvaluatorCallFits body (.fix body continuation)
        values bound) :
    EvaluatorCallFits (.fix body) continuation values bound := by
  exact
    ⟨by simpa [normalSimulationSpace] using call.normal,
      by simpa [ToPartrec.stepNormal] using call.execution⟩

/-- Enlarge the common budget of a fitted code call. -/
theorem mono
    {code : ToPartrec.Code} {continuation : ToPartrec.Cont}
    {values : List Nat} {small large : Nat}
    (call : EvaluatorCallFits code continuation values small)
    (budget : small ≤ large) :
    EvaluatorCallFits code continuation values large where
  normal := call.normal.trans budget
  execution := call.execution.mono budget

end EvaluatorCallFits

/-- A configuration's simulation obligation bounds the corresponding
high-level milestone space. -/
theorem cfgSimulationFits_space
    {configuration : ToPartrec.Cfg} {bound : Nat}
    (fits : cfgSimulationFits configuration bound) :
    evaluatorCfgSpace configuration ≤ bound := by
  cases configuration with
  | halt values =>
      simpa [cfgSimulationFits, evaluatorCfgSpace] using fits
  | ret continuation values =>
      simpa [cfgSimulationFits, evaluatorCfgSpace] using
        retSimulationFits_start fits

/-- A configuration simulation obligation is monotone in its common
budget. -/
theorem cfgSimulationFits_mono
    {configuration : ToPartrec.Cfg} {small large : Nat}
    (fits : cfgSimulationFits configuration small)
    (budget : small ≤ large) :
    cfgSimulationFits configuration large := by
  cases configuration with
  | halt values =>
      exact fits.trans budget
  | ret continuation values =>
      exact retSimulationFits_mono fits budget

/-- A common space certificate for one complete run of a partial-recursive
evaluator.  Besides the structurally normalized initial call, it covers
every sequential evaluator milestone reachable after that call. -/
structure EvaluatorRunFits
    (code : ToPartrec.Code) (values : List Nat) (bound : Nat) :
    Prop where
  normal :
    normalSimulationFits code ToPartrec.Cont.halt values bound
  configuration :
    ∀ current,
      Reaches ToPartrec.step
          (ToPartrec.stepNormal code ToPartrec.Cont.halt values)
          current →
        cfgSimulationFits current bound

namespace EvaluatorRunFits

/-- Numeric upper bounds for the initial normal call and every reachable
configuration suffice for a complete evaluator-run certificate. -/
theorem of_space_le
    {code : ToPartrec.Code} {values : List Nat} {bound : Nat}
    (normal :
      normalSimulationSpace code ToPartrec.Cont.halt values ≤ bound)
    (configuration :
      ∀ current,
        Reaches ToPartrec.step
            (ToPartrec.stepNormal code ToPartrec.Cont.halt values)
            current →
          cfgSimulationSpace current ≤ bound) :
    EvaluatorRunFits code values bound where
  normal :=
    (normalSimulationFits_iff code ToPartrec.Cont.halt
      values bound).2 normal
  configuration := by
    intro current reachable
    exact (cfgSimulationFits_iff current bound).2
      (configuration current reachable)

/-- A fitted call under the halting continuation supplies the complete
run-level certificate. -/
theorem of_call
    {code : ToPartrec.Code} {values : List Nat} {bound : Nat}
    (call :
      EvaluatorCallFits code ToPartrec.Cont.halt values bound) :
    EvaluatorRunFits code values bound :=
  of_space_le call.normal
    (fun _ reachable =>
      call.execution.space_of_reaches reachable)

/-- A step-preserved predicate that supplies the local simulation
obligation is sufficient to certify all reachable evaluator milestones. -/
theorem of_invariant
    {code : ToPartrec.Code} {values : List Nat} {bound : Nat}
    (invariant : ToPartrec.Cfg → Prop)
    (normal :
      normalSimulationFits code ToPartrec.Cont.halt values bound)
    (initial :
      invariant
        (ToPartrec.stepNormal code ToPartrec.Cont.halt values))
    (fits :
      ∀ current, invariant current →
        cfgSimulationFits current bound)
    (preserved :
      ∀ current next,
        invariant current →
        ToPartrec.step current = some next →
        invariant next) :
    EvaluatorRunFits code values bound where
  normal := normal
  configuration := by
    intro current reachable
    apply fits current
    induction reachable with
    | refl =>
        exact initial
    | @tail before after reachable edge induction =>
        apply preserved before after induction
        simpa only [Option.mem_def] using edge

/-- Numeric local bounds plus a step-preserved invariant give a complete
evaluator-run certificate. -/
theorem of_space_invariant
    {code : ToPartrec.Code} {values : List Nat} {bound : Nat}
    (invariant : ToPartrec.Cfg → Prop)
    (normal :
      normalSimulationSpace code ToPartrec.Cont.halt values ≤ bound)
    (initial :
      invariant
        (ToPartrec.stepNormal code ToPartrec.Cont.halt values))
    (space :
      ∀ current, invariant current →
        cfgSimulationSpace current ≤ bound)
    (preserved :
      ∀ current next,
        invariant current →
        ToPartrec.step current = some next →
        invariant next) :
    EvaluatorRunFits code values bound :=
  of_invariant invariant
    ((normalSimulationFits_iff code ToPartrec.Cont.halt
      values bound).2 normal)
    initial
    (fun current holds =>
      (cfgSimulationFits_iff current bound).2
        (space current holds))
    preserved

/-- Enlarge the common budget of a complete evaluator-run certificate. -/
theorem mono
    {code : ToPartrec.Code} {values : List Nat}
    {small large : Nat}
    (fits : EvaluatorRunFits code values small)
    (budget : small ≤ large) :
    EvaluatorRunFits code values large where
  normal := normalSimulationFits_mono fits.normal budget
  configuration := by
    intro current reachable
    exact cfgSimulationFits_mono
      (fits.configuration current reachable) budget

end EvaluatorRunFits

/-- A high-level evaluator run between related milestones can be refined to
a low-level run that stays within the common budget. -/
theorem trCfg_reaches_inSpace_nonempty
    {origin first last : ToPartrec.Cfg} {source : Cfg'}
    {bound : Nat}
    (originToFirst :
      Reaches ToPartrec.step origin first)
    (run : Reaches ToPartrec.step first last)
    (related : TrCfg first source)
    (fits :
      ∀ current,
        Reaches ToPartrec.step origin current →
          cfgSimulationFits current bound) :
    ∃ target,
      TrCfg last target ∧
        Nonempty
          (EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
            source target) := by
  induction run generalizing source with
  | refl =>
      have sourceBound : TM2.stackSpace source ≤ bound := by
        rw [stackSpace_eq_evaluatorCfgSpace_of_TrCfg related]
        exact cfgSimulationFits_space (fits first originToFirst)
      exact
        ⟨source, related,
          ⟨EvalsToInSpace.refl (TM2.step tr) TM2.stackSpace
            bound source sourceBound⟩⟩
  | @tail middle last run edge induction =>
      obtain ⟨middleTarget, middleRelated, ⟨before⟩⟩ :=
        induction related
      have originToMiddle :
          Reaches ToPartrec.step origin middle :=
        originToFirst.trans run
      cases middle with
      | halt values =>
          simp [ToPartrec.step] at edge
      | ret continuation values =>
          have lastEq :
              last = ToPartrec.stepRet continuation values := by
            simpa [ToPartrec.step, Option.mem_def] using edge.symm
          subst last
          rw [TrCfg] at middleRelated
          obtain ⟨state, rfl⟩ := middleRelated
          have returnFits :
              retSimulationFits continuation values bound :=
            fits (.ret continuation values) originToMiddle
          obtain ⟨target, targetRelated, after⟩ :=
            tr_ret_respects_inSpace continuation values state
              bound returnFits
          exact
            ⟨target, targetRelated.down,
              ⟨before.trans after⟩⟩

/-- A terminating high-level evaluation gives a complete bounded run of the
four-stack evaluator from its concrete initial state to its concrete halt
state. -/
theorem evaluator_run_inSpace_nonempty
    (code : ToPartrec.Code) (values output : List Nat)
    (bound : Nat) (fits : EvaluatorRunFits code values bound)
    (evaluates : output ∈ code.eval values) :
    Nonempty
      (EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
        (init code values) (halt output)) := by
  have highEvaluation :
      ToPartrec.Cfg.halt output ∈
        StateTransition.eval ToPartrec.step
          (ToPartrec.stepNormal code ToPartrec.Cont.halt values) := by
    rw [ToPartrec.stepNormal_eval]
    exact (Part.mem_map_iff _).2 ⟨output, evaluates, rfl⟩
  have highRun :
      Reaches ToPartrec.step
        (ToPartrec.stepNormal code ToPartrec.Cont.halt values)
        (.halt output) :=
    (StateTransition.mem_eval.mp highEvaluation).1
  obtain ⟨middle, middleRelated, initialRun⟩ :=
    trNormal_respects_inSpace code ToPartrec.Cont.halt values
      none bound fits.normal
  have initialRun' :
      EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
        (init code values) middle := by
    simpa [init, trCont, trContStack] using initialRun
  obtain ⟨target, targetRelated, ⟨remainingRun⟩⟩ :=
    trCfg_reaches_inSpace_nonempty
      (origin := ToPartrec.stepNormal code ToPartrec.Cont.halt values)
      (first := ToPartrec.stepNormal code ToPartrec.Cont.halt values)
      (last := ToPartrec.Cfg.halt output)
      (source := middle)
      Relation.ReflTransGen.refl highRun middleRelated.down
      fits.configuration
  rw [TrCfg] at targetRelated
  subst target
  exact ⟨initialRun'.trans remainingRun⟩

/-- Noncomputably select the complete bounded evaluator run certified
above. -/
noncomputable def evaluator_run_inSpace
    (code : ToPartrec.Code) (values output : List Nat)
    (bound : Nat) (fits : EvaluatorRunFits code values bound)
    (evaluates : output ∈ code.eval values) :
    EvalsToInSpace (TM2.step tr) TM2.stackSpace bound
      (init code values) (halt output) :=
  Classical.choice
    (evaluator_run_inSpace_nonempty code values output bound
      fits evaluates)

/-- Every concrete four-stack configuration reachable during a certified
terminating evaluator run respects the common space budget. -/
theorem evaluator_reachable_space_le
    (code : ToPartrec.Code) (values output : List Nat)
    (bound : Nat) (fits : EvaluatorRunFits code values bound)
    (evaluates : output ∈ code.eval values)
    {configuration : Cfg'}
    (reachable :
      Reaches (TM2.step tr) (init code values) configuration) :
    TM2.stackSpace configuration ≤ bound := by
  apply
    EvalsToInSpace.space_le_of_terminal
      (evaluator_run_inSpace code values output bound fits evaluates)
      _ reachable
  simp [halt, TM2.step]

/-- Package run-level evaluator certificates directly as the ambient
polynomial-space decider expected by the finite-machine compiler. -/
noncomputable def PolySpaceDecider.ofEvaluatorRunFits
    {α : Type} [Primcodable α] {language : α → Prop}
    (code : ToPartrec.Code) (result : α → Bool)
    (correct : ∀ input, result input = true ↔ language input)
    (evaluates : ∀ input,
      [Encodable.encode (result input)] ∈
        code.eval [Encodable.encode input])
    (space : Polynomial Nat)
    (fits : ∀ input,
      EvaluatorRunFits code [Encodable.encode input]
        (space.eval
          ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
            input).length)) :
    PolySpaceDecider language where
  code := code
  result := result
  correct := correct
  evaluates := evaluates
  space := space
  space_le := by
    intro input configuration reachable
    exact
      evaluator_reachable_space_le code
        [Encodable.encode input]
        [Encodable.encode (result input)]
        (space.eval
          ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
            input).length)
        (fits input) (evaluates input) reachable

/-- Proposition-level PSPACE membership from run-level evaluator
certificates. -/
theorem inPSPACE_of_evaluatorRunFits
    {α : Type} [Primcodable α] {language : α → Prop}
    (code : ToPartrec.Code) (result : α → Bool)
    (correct : ∀ input, result input = true ↔ language input)
    (evaluates : ∀ input,
      [Encodable.encode (result input)] ∈
        code.eval [Encodable.encode input])
    (space : Polynomial Nat)
    (fits : ∀ input,
      EvaluatorRunFits code [Encodable.encode input]
        (space.eval
          ((LeanTrominoes.Complexity.primcodableFinEncoding α).encode
            input).length)) :
    LeanTrominoes.Complexity.InPSPACE
      (LeanTrominoes.Complexity.primcodableFinEncoding α)
      language :=
  inPSPACE_of_partrec
    (PolySpaceDecider.ofEvaluatorRunFits code result correct evaluates
      space fits)

end PartrecToTM2
end Turing
