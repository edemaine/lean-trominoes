/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoSeparation
import LeanTrominoes.PlaneTilingFiniteSearch

/-! # A finite cut test for disconnected polyominoes -/

namespace LeanTrominoes.PolyominoConnectivitySearch

def Cut (input part : List Cell) : Prop :=
  (∃ a ∈ input, a ∈ part) ∧ (∃ b ∈ input, b ∉ part) ∧
    ∀ a ∈ part, ∀ b ∈ input, Cell.SideAdjacent a b → b ∈ part

instance (input part : List Cell) : Decidable (Cut input part) := by
  unfold Cut
  infer_instance

def Disconnected (input : List Cell) : Prop :=
  ∃ part ∈ PlaneTilingSearch.subsets input, Cut input part

instance (input : List Cell) : Decidable (Disconnected input) := by
  unfold Disconnected
  infer_instance

theorem not_connected_of_cut (input part : List Cell) (cut : Cut input part) :
    ¬ Polyomino.IsConnected input.toFinset := by
  obtain ⟨⟨a, ha, inside⟩, ⟨b, hb, outside⟩, closed⟩ := cut
  exact Polyomino.not_connected_of_closed input.toFinset {c | c ∈ part}
    (fun u _ hu v hv edge => closed u hu v (List.mem_toFinset.mp hv) edge)
    a b (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb) inside outside

theorem disconnected_of_not_connected (input : List Cell) (nonempty : input ≠ [])
    (notConnected : ¬ Polyomino.IsConnected input.toFinset) : Disconnected input := by
  classical
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil input nonempty
  let root : {c // c ∈ input.toFinset} := ⟨a, List.mem_toFinset.mpr ha⟩
  have missing : ∃ b, ¬ (Polyomino.sideGraph input.toFinset).Reachable root b := by
    by_contra! all
    exact notConnected ((SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨root, all⟩)
  obtain ⟨b, hb⟩ := missing
  let reachable (c : Cell) : Prop := ∃ hc : c ∈ input.toFinset,
    (Polyomino.sideGraph input.toFinset).Reachable root ⟨c, hc⟩
  let part := input.filter (fun c => decide (reachable c))
  refine ⟨part, PlaneTilingSearch.filter_mem_subsets _ _, ?_⟩
  refine ⟨⟨a, ha, ?_⟩, ⟨b.val, List.mem_toFinset.mp b.property, ?_⟩, ?_⟩
  · simp only [part, List.mem_filter, decide_eq_true_eq]
    exact ⟨ha, root.property, SimpleGraph.Reachable.rfl⟩
  · intro member
    obtain ⟨_, hc, path⟩ : b.val ∈ input ∧ reachable b.val := by simpa [part] using member
    exact hb path
  · intro u hu v hv edge
    obtain ⟨_, hc, path⟩ : u ∈ input ∧ reachable u := by simpa [part] using hu
    simp only [part, List.mem_filter, decide_eq_true_eq]
    refine ⟨hv, List.mem_toFinset.mpr hv, ?_⟩
    exact path.trans (SimpleGraph.Adj.reachable (G := Polyomino.sideGraph input.toFinset) edge)

theorem disconnected_iff (input : List Cell) (nonempty : input ≠ []) :
    Disconnected input ↔ ¬ Polyomino.IsConnected input.toFinset := by
  constructor
  · rintro ⟨part, _, cut⟩
    exact not_connected_of_cut input part cut
  · exact disconnected_of_not_connected input nonempty

end LeanTrominoes.PolyominoConnectivitySearch
