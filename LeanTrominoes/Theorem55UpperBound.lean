/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55
import LeanTrominoes.PolyominoConnectivityComputability

/-! # The co-r.e. upper bound for the connected/disconnected plane target -/

namespace LeanTrominoes.Theorem55

noncomputable def searchInput (input : List Cell) : PlaneTilingSearch.Input :=
  (PlusRefinement.bumpy.toList, input)

theorem searchInput_tiles (input : List Cell) :
    PlaneTilingSearch.tiles (searchInput input) = pairTiles PlusRefinement.bumpy input.toFinset := by
  funext kind
  cases kind <;> simp [searchInput, PlaneTilingSearch.tiles, PlaneTilingSearch.tileList, pairTiles]

def FiniteCheck (input : List Cell) (radius : Nat) : Prop :=
  input ≠ [] ∧ PolyominoConnectivitySearch.Disconnected input ∧
    PlaneTilingSearch.FiniteSearch (searchInput input) radius

theorem finiteCheck_primrec : PrimrecRel FiniteCheck := by
  have compiler : Primrec searchInput := Primrec.pair (Primrec.const PlusRefinement.bumpy.toList) Primrec.id
  exact (Primrec.eq.comp Primrec.fst (Primrec.const [])).not.and
    ((PolyominoConnectivitySearch.disconnected_primrec.comp Primrec.fst).and
      (PlaneTilingSearch.finiteSearch_primrec.comp (compiler.comp Primrec.fst) Primrec.snd))

theorem planeProblem_iff_all_finiteCheck (input : List Cell) :
    planeProblem input ↔ ∀ radius, FiniteCheck input radius := by
  have nonempty : input.toFinset.Nonempty ↔ input ≠ [] := by simp
  simp only [planeProblem, nonempty]
  constructor
  · rintro ⟨hn, hd, ht⟩ radius
    refine ⟨hn, (PolyominoConnectivitySearch.disconnected_iff input hn).mpr hd, ?_⟩
    apply PlaneTilingSearch.finiteSearch_of_tileable
    rwa [searchInput_tiles]
  · intro all
    obtain ⟨hn, hd, _⟩ := all 0
    refine ⟨hn, (PolyominoConnectivitySearch.disconnected_iff input hn).mp hd, ?_⟩
    rw [← searchInput_tiles]
    exact PlaneTilingSearch.tileable_of_all_finiteSearch _ (fun radius => (all radius).2.2)

theorem coRE : LeanWang.CoREPred planeProblem := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input radius => ¬ FiniteCheck input radius) finiteCheck_primrec.not.computablePred
  exact obstruction.of_eq (fun input => by
    change (∃ radius, ¬ FiniteCheck input radius) ↔ ¬ planeProblem input
    rw [planeProblem_iff_all_finiteCheck]
    exact not_forall.symm)

end LeanTrominoes.Theorem55
