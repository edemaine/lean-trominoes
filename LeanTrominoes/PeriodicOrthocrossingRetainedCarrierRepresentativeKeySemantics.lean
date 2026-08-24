/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyBlockSemantics

/-! # Neighboring-key presentation of retained representative carriers -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Filtering indices whose blocks are empty preserves the exact flattened
output order. -/
private theorem flatMap_eq_filter_of_rejected_empty
    {Index Output : Type}
    (indices : List Index) (predicate : Index → Prop)
    [DecidablePred predicate]
    (blocks : Index → List Output)
    (rejectedEmpty :
      ∀ index ∈ indices, ¬predicate index → blocks index = []) :
    indices.flatMap blocks =
      (indices.filter fun index => predicate index).flatMap blocks := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      have tailEmpty :
          ∀ tail ∈ indices, ¬predicate tail → blocks tail = [] := by
        intro tail tailMember rejected
        exact rejectedEmpty tail
          (List.mem_cons_of_mem index tailMember) rejected
      rw [List.flatMap_cons, induction tailEmpty]
      by_cases accepted : predicate index
      · simp [accepted]
      · rw [rejectedEmpty index (List.mem_cons_self) accepted]
        simp [accepted]

/-- Halo-only keys contribute no representative links, so restricting the
original retained key order to neighboring occurrences leaves the selected
carrier-link list exactly unchanged. -/
theorem retainedDrawingCompleteCarrierLinks_eq_neighboring
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedDrawingCompleteCarrierLinks graph =
      retainedNeighboringCarrierLinks graph := by
  rw [retainedDrawingCompleteCarrierLinks_eq_keyBlocks]
  unfold retainedNeighboringCarrierLinks retainedNeighboringCarrierKeys
  apply flatMap_eq_filter_of_rejected_empty
  intro key keyMember notNeighboring
  exact retainedRepresentativeCarrierLinksAt_eq_nil_of_not_neighboring
    graph key keyMember notNeighboring

end LeanTrominoes.PeriodicOrthocrossing
