/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoConnectedPolycubes
import LeanTrominoes.PolycubeSearchComputability
import LeanTrominoes.PolycubeConnectivityComputability

/-! # Co-r.e. upper bounds for two connected polycubes -/

namespace LeanTrominoes.TwoConnectedPolycubes

noncomputable def searchInput (small : Polycube) (input : List Voxel) : VoxelTilingSearch.Input :=
  (small.toList, input)

theorem searchInput_tiles (small : Polycube) (input : List Voxel) :
    VoxelTilingSearch.tiles (searchInput small input) = Polycube.pairTiles small input.toFinset := by
  funext kind
  cases kind <;> simp [searchInput, VoxelTilingSearch.tiles, VoxelTilingSearch.tileList, Polycube.pairTiles]

def FiniteCheck (small : Polycube) (region : Set Voxel) (input : List Voxel) (radius : Nat) : Prop :=
  Polycube.IsConnected input.toFinset ∧ VoxelTilingSearch.FiniteSearch (searchInput small input) region radius

theorem finiteCheck_primrec (small : Polycube) (region : Set Voxel)
    (regionPR : PrimrecPred (fun c => c ∈ region)) : PrimrecRel (FiniteCheck small region) := by
  have compiler : Primrec (searchInput small) := Primrec.pair (Primrec.const small.toList) Primrec.id
  exact (PolycubeConnectivitySearch.connected_primrec.comp Primrec.fst).and
    ((VoxelTilingSearch.finiteSearch_primrec region regionPR).comp (compiler.comp Primrec.fst) Primrec.snd)

theorem problem_iff_all_finiteCheck (small : Polycube) (region : Set Voxel) (input : List Voxel) :
    problem small region input ↔ ∀ radius, FiniteCheck small region input radius := by
  constructor
  · rintro ⟨hc, ht⟩ radius
    refine ⟨hc, VoxelTilingSearch.finiteSearch_of_tileable _ region ?_ radius⟩
    rwa [searchInput_tiles]
  · intro all
    refine ⟨(all 0).1, ?_⟩
    rw [← searchInput_tiles]
    exact VoxelTilingSearch.tileable_of_all_finiteSearch _ region (fun radius => (all radius).2)

theorem problem_coRE (small : Polycube) (region : Set Voxel)
    (regionPR : PrimrecPred (fun c => c ∈ region)) : LeanWang.CoREPred (problem small region) := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input radius => ¬ FiniteCheck small region input radius)
    (finiteCheck_primrec small region regionPR).not.computablePred
  exact obstruction.of_eq (fun input => by
    change (∃ radius, ¬ FiniteCheck small region input radius) ↔ ¬ problem small region input
    rw [problem_iff_all_finiteCheck]
    exact not_forall.symm)

theorem slab_coRE (small : Polycube) (height : Nat) :
    LeanWang.CoREPred (problem small (voxelSlab height)) := by
  apply problem_coRE
  exact (Computability.int_le_primrec.comp (Primrec.const 0) Primrec.snd).and
    (Computability.int_lt_primrec.comp Primrec.snd (Primrec.const (height : Int)))

theorem slabTwo_coRE : LeanWang.CoREPred slabTwoProblem := slab_coRE _ _

theorem space_coRE : LeanWang.CoREPred spaceProblem :=
  problem_coRE _ _ ((Primrec.eq.comp Primrec.id Primrec.id).of_eq (fun _ => by simp))

end LeanTrominoes.TwoConnectedPolycubes
