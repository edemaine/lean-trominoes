/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyData
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeOccurrence

/-! # Semantics of per-key retained representative carrier blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Filtering the raw retained family distributes into its physical-key
blocks without changing their order. -/
theorem retainedDrawingCompleteCarrierLinks_eq_keyBlocks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedDrawingCompleteCarrierLinks graph =
      (retainedDrawingCompleteCarrierKeys graph).flatMap
        (retainedRepresentativeCarrierLinksAt graph) := by
  unfold retainedDrawingCompleteCarrierLinks
    retainedDrawingCompleteCarrierLinksRaw
    retainedRepresentativeCarrierLinksAt
  rw [List.filter_flatMap]

/-- A retained physical key outside the neighboring occurrence window has no
selected representative-link block. -/
theorem retainedRepresentativeCarrierLinksAt_eq_nil_of_not_neighboring
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell)
    (keyMember : key ∈ retainedDrawingCompleteCarrierKeys graph)
    (notNeighboring : key ∉ neighboringCarrierKeys graph) :
    retainedRepresentativeCarrierLinksAt graph key = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro link linkMember representative
  have selectedMember :
      link ∈ retainedDrawingCompleteCarrierLinks graph :=
    (mem_retainedDrawingCompleteCarrierLinks_iff graph link).mpr
      ⟨List.mem_flatMap.mpr ⟨key, keyMember, linkMember⟩,
        of_decide_eq_true representative⟩
  have keyEq :=
    (retainedCompleteCarrierLinks_common_key
      graph key linkMember).1
  apply notNeighboring
  rw [← keyEq]
  exact retainedDrawingCompleteCarrierLink_key_mem_neighborOccurrences
    selectedMember

end LeanTrominoes.PeriodicOrthocrossing
