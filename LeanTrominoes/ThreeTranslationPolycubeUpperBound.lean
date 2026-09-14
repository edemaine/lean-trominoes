/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubeGeometry
import LeanTrominoes.TranslationVoxelSearch
import LeanTrominoes.TwoConnectedPolycubesUpperBound
import LeanTrominoes.PolycubeConnectivityComputability

/-! # Co-r.e. upper bounds for three translation-only connected polycubes -/

namespace LeanTrominoes.ThreeTranslationPolycubes
open TwoConnectedPolycubes (searchInput searchInput_tiles)

def FiniteCheck (layers : Finset Int) (region : Set Voxel) (input : List Voxel) (radius : Nat) : Prop :=
  Polycube.IsConnected input.toFinset ∧ TranslationVoxelSearch.FiniteSearch (searchInput (Polycube.extrude PlusRefinement.bumpy layers) input) region radius

theorem finiteCheck_primrec (layers : Finset Int) (region : Set Voxel)
    (regionPR : PrimrecPred (fun c => c ∈ region)) : PrimrecRel (FiniteCheck layers region) := by
  have compiler : Primrec (searchInput (Polycube.extrude PlusRefinement.bumpy layers)) := Primrec.pair (Primrec.const (Polycube.extrude PlusRefinement.bumpy layers).toList) Primrec.id
  exact (PolycubeConnectivitySearch.connected_primrec.comp Primrec.fst).and
    ((TranslationVoxelSearch.finiteSearch_primrec region regionPR).comp (compiler.comp Primrec.fst) Primrec.snd)

theorem problem_iff_all_finiteCheck (layers : Finset Int) (region : Set Voxel) (input : List Voxel) :
    problem layers region input ↔ ∀ radius, FiniteCheck layers region input radius := by
  constructor
  · rintro ⟨hc, ht⟩ radius
    refine ⟨hc, TranslationVoxelSearch.finiteSearch_of_tileable _ region ?_ radius⟩
    rw [searchInput_tiles]
    exact (translationTileable_iff _ _ _).mp ht
  · intro all
    refine ⟨(all 0).1, ?_⟩
    apply (translationTileable_iff _ _ _).mpr
    rw [← searchInput_tiles]
    exact TranslationVoxelSearch.tileable_of_all_finiteSearch _ region (fun radius => (all radius).2)

theorem problem_coRE (layers : Finset Int) (region : Set Voxel)
    (regionPR : PrimrecPred (fun c => c ∈ region)) : LeanWang.CoREPred (problem layers region) := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input radius => ¬ FiniteCheck layers region input radius)
    (finiteCheck_primrec layers region regionPR).not.computablePred
  exact obstruction.of_eq (fun input => by
    change (∃ radius, ¬ FiniteCheck layers region input radius) ↔ ¬ problem layers region input
    rw [problem_iff_all_finiteCheck]
    exact not_forall.symm)

theorem slab_coRE (height : Nat) :
    LeanWang.CoREPred (slabProblem height) := by
  apply problem_coRE
  exact (Computability.int_le_primrec.comp (Primrec.const 0) Primrec.snd).and
    (Computability.int_lt_primrec.comp Primrec.snd (Primrec.const (height : Int)))

theorem space_coRE : LeanWang.CoREPred spaceProblem :=
  problem_coRE _ _ ((Primrec.eq.comp Primrec.id Primrec.id).of_eq (fun _ => by simp))

end LeanTrominoes.ThreeTranslationPolycubes
