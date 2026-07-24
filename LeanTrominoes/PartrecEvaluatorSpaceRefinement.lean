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
