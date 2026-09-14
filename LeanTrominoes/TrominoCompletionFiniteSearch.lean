/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTrominoCompletion
import LeanTrominoes.FiniteSearch

/-! # Finite obstructions to completing a valid prefill

This supplies the semantic finite-search characterization. `CompletionCoRE`
certifies a computable periodic-input checker, including prefill validity,
and proves plane co-r.e. membership for both trominoes.
-/

namespace LeanTrominoes

theorem Tromino.completable_iff_all_boxes (t : Tromino) (region : Set Cell)
    (prescribed : Set (Finset Cell)) (legal : t.IsPartialTiling region prescribed) :
    t.Completable region prescribed ↔ ∀ radius,
      TrominoAssignment.IsBoxSatisfiable t (region \ Tromino.occupied prescribed) radius := by
  rw [Tromino.completable_iff,and_iff_right legal,
    TrominoAssignment.tileable_iff_forall_isBoxSatisfiable]

namespace PeriodicTrominoPrefill

/-- A finite box check using the executable full-rank membership test. -/
def BoxSatisfiable (t : Tromino) (input : PeriodicTrominoPrefill) (radius : Nat) : Prop :=
  TrominoAssignment.IsBoxSatisfiable t {c | (input.occupiedRegion t).contains c = false} radius

instance (t : Tromino) (input : PeriodicTrominoPrefill) (radius : Nat) :
    Decidable (BoxSatisfiable t input radius) := by
  unfold BoxSatisfiable
  letI : DecidablePred ({c | (input.occupiedRegion t).contains c = false} : Set Cell) :=
    fun c => inferInstanceAs (Decidable ((input.occupiedRegion t).contains c = false))
  infer_instance

theorem planeProblem_iff_all_boxes (t : Tromino) (input : PeriodicTrominoPrefill)
    (rank : (input.occupiedRegion t).IsFullRank) :
    planeProblem t input ↔ t.IsPartialTiling Set.univ (input.prescribed t) ∧
      ∀ radius, BoxSatisfiable t input radius := by
  have carrier : {c | (input.occupiedRegion t).contains c = false} =
      (input.occupiedRegion t).carrierᶜ := by
    ext c
    have eq := (input.occupiedRegion t).contains_eq_true_iff rank c
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff]
    rw [← eq]
    cases (input.occupiedRegion t).contains c <;> simp
  rw [planeProblem_iff,and_iff_right rank,
    TrominoAssignment.tileable_iff_forall_isBoxSatisfiable]
  simp only [BoxSatisfiable,carrier]

/-- A valid full-rank periodic prefill fails to extend iff some finite box
has no satisfying assignment on the uncovered cells. -/
theorem not_planeProblem_iff (t : Tromino) (input : PeriodicTrominoPrefill)
    (rank : (input.occupiedRegion t).IsFullRank)
    (legal : t.IsPartialTiling Set.univ (input.prescribed t)) :
    ¬ planeProblem t input ↔ ∃ radius, ¬ BoxSatisfiable t input radius := by
  classical
  rw [planeProblem_iff_all_boxes t input rank,and_iff_right legal,not_forall]

end PeriodicTrominoPrefill

namespace PeriodicStripTrominoPrefill

/-- The same semantic obstruction criterion applies in bounded-height strips. -/
theorem problem_iff_all_boxes (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (height : 0 < input.height) (period : 0 < input.period)
    (legal : t.IsPartialTiling input.region (input.periodic.prescribed t)) :
    problem t input ↔ ∀ radius, TrominoAssignment.IsBoxSatisfiable t
      (input.region \ (input.periodic.occupiedRegion t).carrier) radius := by
  rw [problem_iff,and_iff_right height,and_iff_right period,and_iff_right legal,
    TrominoAssignment.tileable_iff_forall_isBoxSatisfiable]

end PeriodicStripTrominoPrefill
end LeanTrominoes
