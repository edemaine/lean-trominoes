/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeConnectivitySearch
import LeanTrominoes.PolyominoConnectivityComputability
import LeanTrominoes.PlaneTilingSearchComputability

/-! # Computability of finite polycube cut certificates -/

namespace LeanTrominoes.PolycubeConnectivitySearch

open Computability

theorem mem_list_primrec : PrimrecRel (fun (c : Voxel) (xs : List Voxel) => c ∈ xs) := by
  apply (Primrec.eq.exists_mem_list.comp₂ Primrec₂.right Primrec₂.left).of_eq
  intro c xs
  simp

theorem adjacent_primrec : PrimrecRel Voxel.FaceAdjacent := by
  have xyA : Primrec (fun a : Voxel × Voxel => a.1.1) := Primrec.fst.comp Primrec.fst
  have zA : Primrec (fun a : Voxel × Voxel => a.1.2) := Primrec.snd.comp Primrec.fst
  have xyB : Primrec (fun a : Voxel × Voxel => a.2.1) := Primrec.fst.comp Primrec.snd
  have zB : Primrec (fun a : Voxel × Voxel => a.2.2) := Primrec.snd.comp Primrec.snd
  exact ((Primrec.eq.comp zA zB).and
    (PolyominoConnectivitySearch.adjacent_primrec.comp xyA xyB)).or
    ((Primrec.eq.comp xyA xyB).and
      ((Primrec.eq.comp (int_add_primrec.comp zA (Primrec.const 1)) zB).or
        (Primrec.eq.comp (int_add_primrec.comp zB (Primrec.const 1)) zA)))

theorem cut_primrec : PrimrecRel Cut := by
  have inside : PrimrecRel (fun (c : Voxel) (a : List Voxel × List Voxel) => c ∈ a.2) :=
    mem_list_primrec.comp₂ Primrec₂.left (Primrec.snd.comp₂ Primrec₂.right)
  have row : PrimrecRel (fun (b : Voxel) (a : (List Voxel × List Voxel) × Voxel) =>
      Voxel.FaceAdjacent a.2 b → b ∈ a.1.2) := by
    apply ((adjacent_primrec.comp₂ (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left).not.or
      (mem_list_primrec.comp₂ Primrec₂.left
        (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.right)))).of_eq
    intro a
    tauto
  have rows : PrimrecRel (fun (c : Voxel) (a : List Voxel × List Voxel) =>
      ∀ b ∈ a.1, Voxel.FaceAdjacent c b → b ∈ a.2) :=
    row.forall_mem_list.comp (Primrec.fst.comp Primrec.snd) (Primrec.pair Primrec.snd Primrec.fst)
  exact (inside.exists_mem_list.comp Primrec.fst Primrec.id).and
    ((inside.not.exists_mem_list.comp Primrec.fst Primrec.id).and
      (rows.forall_mem_list.comp Primrec.snd Primrec.id))

theorem disconnected_primrec : PrimrecPred Disconnected :=
  cut_primrec.swap.exists_mem_list.comp PlaneTilingSearch.subsets_primrec Primrec.id

theorem connected_primrec : PrimrecPred (fun input : List Voxel =>
    Polycube.IsConnected input.toFinset) :=
  ((Primrec.eq.comp Primrec.id (Primrec.const [])).not.and disconnected_primrec.not).of_eq
    (fun input => (connected_iff input).symm)

end LeanTrominoes.PolycubeConnectivitySearch
