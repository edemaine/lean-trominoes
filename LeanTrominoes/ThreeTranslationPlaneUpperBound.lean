/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TranslationPlaneSearch
import LeanTrominoes.Theorem55UpperBound

/-! # Co-r.e. membership with translation-only background placements -/

namespace LeanTrominoes.ThreeTranslationPolyominoes
open Theorem55 (searchInput searchInput_tiles)

def FiniteCheck (input : List Cell) (radius : Nat) : Prop :=
  input ≠ [] ∧ PolyominoConnectivitySearch.Disconnected input ∧
    TranslationPlaneSearch.FiniteSearch (searchInput input) radius

theorem finiteCheck_primrec : PrimrecRel FiniteCheck := by
  have compiler : Primrec searchInput := Primrec.pair (Primrec.const PlusRefinement.bumpy.toList) Primrec.id
  exact (Primrec.eq.comp Primrec.fst (Primrec.const [])).not.and
    ((PolyominoConnectivitySearch.disconnected_primrec.comp Primrec.fst).and
      (TranslationPlaneSearch.finiteSearch_primrec.comp (compiler.comp Primrec.fst) Primrec.snd))

theorem planeProblem_iff_all_finiteCheck (input : List Cell) :
    planeProblem input ↔ ∀ radius, FiniteCheck input radius := by
  have nonempty : input.toFinset.Nonempty ↔ input ≠ [] := by simp
  simp only [planeProblem,nonempty]
  constructor
  · rintro ⟨hn,hd,ht⟩ radius
    refine ⟨hn,(PolyominoConnectivitySearch.disconnected_iff input hn).mpr hd,?_⟩
    apply TranslationPlaneSearch.finiteSearch_of_tileable
    rw [searchInput_tiles]
    exact (translationTileable_iff _ _).mp ht
  · intro all
    obtain ⟨hn,hd,_⟩ := all 0
    refine ⟨hn,(PolyominoConnectivitySearch.disconnected_iff input hn).mp hd,?_⟩
    apply (translationTileable_iff _ _).mpr
    rw [← searchInput_tiles]
    exact TranslationPlaneSearch.tileable_of_all_finiteSearch _ (fun radius => (all radius).2.2)

theorem plane_coRE : LeanWang.CoREPred planeProblem := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input radius => ¬ FiniteCheck input radius) finiteCheck_primrec.not.computablePred
  exact obstruction.of_eq (fun input => by
    change (∃ radius, ¬ FiniteCheck input radius) ↔ ¬ planeProblem input
    rw [planeProblem_iff_all_finiteCheck]
    exact not_forall.symm)

end LeanTrominoes.ThreeTranslationPolyominoes
