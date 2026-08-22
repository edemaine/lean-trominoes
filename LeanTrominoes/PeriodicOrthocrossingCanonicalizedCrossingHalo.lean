/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingNormalization

/-! # Canonical crossing keys represented by the physical halo -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Period-normalize every physical halo crossing and retain the last copy
of each resulting canonical key. -/
def canonicalizedCrossingHalo
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List CrossingRecord :=
  ((orientedCrossingHalo graph).map fun crossing =>
    crossing.periodNormalize graph).dedup

theorem canonicalizedCrossingHalo_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (canonicalizedCrossingHalo graph).Nodup := by
  exact List.nodup_dedup _

/-- The canonicalized halo contains exactly the ordinary canonical oriented
crossings; only their presentation order may differ. -/
theorem mem_canonicalizedCrossingHalo_iff
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (crossing : CrossingRecord) :
    crossing ∈ canonicalizedCrossingHalo graph ↔
      crossing ∈ orientedCrossings graph := by
  unfold canonicalizedCrossingHalo
  rw [List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨physical, physicalMember, rfl⟩
    exact periodNormalize_mem_orientedCrossings
      wellFormed degree isLocal physicalMember
  · intro crossingMember
    refine ⟨crossing,
      orientedCrossings_subset_orientedCrossingHalo
        graph crossingMember, ?_⟩
    exact periodNormalize_eq_self_of_mem_orientedCrossings
      graph crossingMember

/-- Canonicalizing the physical halo changes only the order of the canonical
crossing list. -/
theorem canonicalizedCrossingHalo_perm_orientedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    List.Perm (canonicalizedCrossingHalo graph)
      (orientedCrossings graph) := by
  apply (List.perm_ext_iff_of_nodup
    (canonicalizedCrossingHalo_nodup graph)
    (orientedCrossings_nodup graph)).mpr
  intro crossing
  exact mem_canonicalizedCrossingHalo_iff
    wellFormed degree isLocal crossing

theorem canonicalizedCrossingHalo_length
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    (canonicalizedCrossingHalo graph).length =
      (orientedCrossings graph).length :=
  (canonicalizedCrossingHalo_perm_orientedCrossings
    wellFormed degree isLocal).length_eq

end PeriodicOrthocrossing
end LeanTrominoes
