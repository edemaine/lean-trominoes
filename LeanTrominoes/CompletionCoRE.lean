/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ComputableRegionSearch
import LeanTrominoes.CompletionPrefillComputability
import LeanTrominoes.TrominoCompletionFiniteSearch

/-! # Co-r.e. membership of periodic tromino completion

A no-instance has a finite witness: dependent period vectors, two distinct
overlapping prescribed tiles, or an unsatisfiable finite box of uncovered
cells. The search applies to both trominoes and arbitrary input prefills.
-/

namespace LeanTrominoes.PeriodicTrominoPrefill
open Computability TrominoAssignment TrominoAssignment.ComputableRegionSearch

/-- Executable membership in the uncovered region on full-rank inputs. -/
def uncovered (t : Tromino) (input : PeriodicTrominoPrefill) (c : Cell) : Bool :=
  !(input.occupiedRegion t).validContains c

theorem uncovered_primrec (t : Tromino) : Primrec₂ (uncovered t) :=
  (Primrec.dom_finite Bool.not).comp
    (periodicRegion_validContains_primrec.comp ((occupiedRegion_primrec t).comp Primrec.fst) Primrec.snd)

theorem uncovered_eq (t : Tromino) (input : PeriodicTrominoPrefill)
    (rank : (input.occupiedRegion t).IsFullRank) :
    {c | uncovered t input c = true} = (input.occupiedRegion t).carrierᶜ := by
  ext c
  change (!(input.occupiedRegion t).validContains c) = true ↔ c ∉ (input.occupiedRegion t).carrier
  have eq := (input.occupiedRegion t).validContains_eq_true_iff c
  simp only [rank,true_and] at eq
  rw [← eq]
  cases (input.occupiedRegion t).validContains c <;> decide

/-- All three finite tests performed at a search stage. -/
def Check (t : Tromino) (input : PeriodicTrominoPrefill) (radius : Nat) : Prop :=
  (input.occupiedRegion t).IsFullRank ∧ BoundedValid t input radius ∧
    IsComputableListBoxSatisfiable (uncovered t) t input radius

theorem check_primrec (t : Tromino) : PrimrecPred fun input : PeriodicTrominoPrefill × Nat =>
    Check t input.1 input.2 :=
  (periodicRegion_isFullRank_primrec.comp ((occupiedRegion_primrec t).comp Primrec.fst)).and
    ((boundedValid_primrec t).and (isComputableListBoxSatisfiable_primrec (uncovered_primrec t) t))

theorem planeProblem_iff_checks (t : Tromino) (input : PeriodicTrominoPrefill) :
    planeProblem t input ↔ ∀ radius, Check t input radius := by
  have search (rank : (input.occupiedRegion t).IsFullRank) :
      t.Tileable (input.occupiedRegion t).carrierᶜ ↔
        ∀ radius, IsComputableListBoxSatisfiable (uncovered t) t input radius := by
    rw [tileable_iff_forall_isBoxSatisfiable]
    apply forall_congr'
    intro radius
    rw [isComputableListBoxSatisfiable_iff,uncovered_eq t input rank]
  rw [planeProblem_iff,partial_iff_bounded]
  constructor
  · rintro ⟨rank,valid,tiled⟩ radius
    exact ⟨rank,valid radius,(search rank).mp tiled radius⟩
  · intro checked
    have rank := (checked 0).1
    exact ⟨rank,fun r => (checked r).2.1,(search rank).mpr fun r => (checked r).2.2⟩

/-- Completing a periodic prefill in the plane belongs to co-r.e., for either
L- or I-trominoes. Completing tilings are not required to be periodic. -/
theorem planeProblem_coRE (t : Tromino) : LeanWang.CoREPred (planeProblem t) := by
  have re : REPred fun input : PeriodicTrominoPrefill => ∃ radius, ¬ Check t input radius :=
    LeanWang.REPred.exists_nat (check_primrec t).not.computablePred
  exact re.of_eq fun input => by
    rw [planeProblem_iff_checks]
    simp only [not_forall]

end LeanTrominoes.PeriodicTrominoPrefill
