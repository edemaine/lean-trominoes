/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCompleteness
import LeanTrominoes.CompletionPeriodicComputability
import LeanTrominoes.CompletionPeriodicExtraction
import Mathlib.Computability.Halting

/-! # Periodic tromino prefills with no doubly periodic completion

For each tromino there is a valid, doubly periodic prefill admitting a plane
tiling, but no completion has two independent translation periods. The proof
uses finite certificates for doubly periodic completions and co-r.e. hardness.
It does not assert that each completion has no single nonzero period.
-/
namespace LeanTrominoes.PeriodicTrominoPrefill
open CompletionPeriodic

/-- Plane completion is not recursively enumerable for either tromino. -/
theorem planeProblem_not_re (t : Tromino) : ¬ REPred (planeProblem t) := by
  intro re
  obtain ⟨reduce,computable,correct⟩ := planeProblem_coREHard t
    (fun c : Nat.Partrec.Code => ¬ (Nat.Partrec.Code.eval c 0).Dom)
    (by simpa only [LeanWang.CoREPred,not_not] using ComputablePred.halting_problem_re 0)
  exact ComputablePred.halting_problem_not_re 0
    ((LeanWang.REPred.comp re computable).of_eq (fun c => (correct c).symm))

/-- Some completable full-rank prefill has no finite periodic certificate. -/
theorem exists_uncertified_completion (t : Tromino) :
    ∃ input, planeProblem t input ∧ ¬ Certified t input := by
  classical
  by_contra absent
  have eq (input) : Certified t input ↔ planeProblem t input := by
    constructor
    · rintro ⟨rank,w,checked⟩
      exact ⟨rank,check_completable t input w checked⟩
    · intro completed
      by_contra uncertified
      exact absent ⟨input,completed,uncertified⟩
  exact planeProblem_not_re t ((certified_re t).of_eq eq)

/-- For either tromino, a periodic prefill can be completable although no
completion is invariant under any full-rank lattice of translations. -/
theorem exists_no_doubly_periodic_completion (t : Tromino) :
    ∃ input : PeriodicTrominoPrefill,
      (input.occupiedRegion t).IsFullRank ∧
      t.IsPartialTiling Set.univ (input.prescribed t) ∧
      t.Completable Set.univ (input.prescribed t) ∧
      ∀ completed, t.IsFootprintTiling Set.univ completed →
        input.prescribed t ⊆ completed → ¬ HasIndependentPeriods completed := by
  obtain ⟨input,⟨rank,completable⟩,uncertified⟩ := exists_uncertified_completion t
  refine ⟨input,rank,(Tromino.completable_iff _ _ _).mp completable |>.1,completable,?_⟩
  intro completed tiling retained periodic
  obtain ⟨n,hn,square⟩ := squarePeriod_of_independent periodic
  exact uncertified ⟨rank,certificate_of_periodic t input ⟨completed,tiling,retained,n,hn,square⟩⟩
end LeanTrominoes.PeriodicTrominoPrefill
