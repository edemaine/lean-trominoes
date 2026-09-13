/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeConnectivity
import LeanTrominoes.PlaneTilingFiniteSearch

/-! # A finite cut test for disconnected polycubes -/

namespace LeanTrominoes.Polycube

/-- A nonempty proper group of cells closed under side adjacency witnesses
disconnectedness. -/
theorem not_connected_of_closed (shape : Polycube) (part : Set Voxel)
    (closed : ∀ a ∈ shape, a ∈ part → ∀ b ∈ shape, Voxel.FaceAdjacent a b → b ∈ part)
    (a b : Voxel) (ha : a ∈ shape) (hb : b ∈ shape) (inside : a ∈ part) (outside : b ∉ part) :
    ¬ IsConnected shape := by
  intro connected
  change shape.faceGraph.Connected at connected
  have invariant {u v : {c // c ∈ shape}} (walk : shape.faceGraph.Walk u v) :
      u.val ∈ part → v.val ∈ part := by
    induction walk with
    | nil => exact id
    | @cons u v w edge walk ih =>
      intro hu
      exact ih (closed u.val u.property hu v.val v.property edge)
  obtain ⟨walk⟩ := connected ⟨a, ha⟩ ⟨b, hb⟩
  exact outside (invariant walk inside)

end LeanTrominoes.Polycube

namespace LeanTrominoes.PolycubeConnectivitySearch

def Cut (input part : List Voxel) : Prop :=
  (∃ a ∈ input, a ∈ part) ∧ (∃ b ∈ input, b ∉ part) ∧
    ∀ a ∈ part, ∀ b ∈ input, Voxel.FaceAdjacent a b → b ∈ part

instance (input part : List Voxel) : Decidable (Cut input part) := by
  unfold Cut
  infer_instance

def Disconnected (input : List Voxel) : Prop :=
  ∃ part ∈ PlaneTilingSearch.subsets input, Cut input part

instance (input : List Voxel) : Decidable (Disconnected input) := by
  unfold Disconnected
  infer_instance

theorem not_connected_of_cut (input part : List Voxel) (cut : Cut input part) :
    ¬ Polycube.IsConnected input.toFinset := by
  obtain ⟨⟨a, ha, inside⟩, ⟨b, hb, outside⟩, closed⟩ := cut
  exact Polycube.not_connected_of_closed input.toFinset {c | c ∈ part}
    (fun u _ hu v hv edge => closed u hu v (List.mem_toFinset.mp hv) edge)
    a b (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb) inside outside

theorem disconnected_of_not_connected (input : List Voxel) (nonempty : input ≠ [])
    (notConnected : ¬ Polycube.IsConnected input.toFinset) : Disconnected input := by
  classical
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil input nonempty
  let root : {c // c ∈ input.toFinset} := ⟨a, List.mem_toFinset.mpr ha⟩
  have missing : ∃ b, ¬ (Polycube.faceGraph input.toFinset).Reachable root b := by
    by_contra! all
    exact notConnected ((SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨root, all⟩)
  obtain ⟨b, hb⟩ := missing
  let reachable (c : Voxel) : Prop := ∃ hc : c ∈ input.toFinset,
    (Polycube.faceGraph input.toFinset).Reachable root ⟨c, hc⟩
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
    exact path.trans (SimpleGraph.Adj.reachable (G := Polycube.faceGraph input.toFinset) edge)

theorem disconnected_iff (input : List Voxel) (nonempty : input ≠ []) :
    Disconnected input ↔ ¬ Polycube.IsConnected input.toFinset := by
  constructor
  · rintro ⟨part, _, cut⟩
    exact not_connected_of_cut input part cut
  · exact disconnected_of_not_connected input nonempty

theorem connected_iff (input : List Voxel) :
    Polycube.IsConnected input.toFinset ↔ input ≠ [] ∧ ¬ Disconnected input := by
  constructor
  · intro connected
    have hn : input ≠ [] := by
      intro empty
      obtain ⟨c⟩ := connected.nonempty
      have hc := c.property
      change c.val ∈ input.toFinset at hc
      simp [empty] at hc
    exact ⟨hn, fun hd => (disconnected_iff input hn).mp hd connected⟩
  · rintro ⟨hn, hd⟩
    by_contra disconnected
    exact hd ((disconnected_iff input hn).mpr disconnected)

end LeanTrominoes.PolycubeConnectivitySearch
