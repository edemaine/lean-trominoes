/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionBarrier

/-! # Excluding a crossing tile by a nearby cell that it would strand -/

namespace LeanTrominoes.CompletionBarrier

/-- A candidate leaves a cell uncovered for which every covering tile would
hit a blocked cell or overlap the candidate. -/
def ConflictCheck (t : Tromino) (blocked available f : Finset Cell) : Prop :=
  ∃ c ∈ available, c ∉ f ∧ ∀ p ∈ TrominoAssignment.coveringPlacementList t c,
    ¬ Disjoint (p.cells (fun _ => t.cells)) blocked ∨
      ¬ Disjoint (p.cells (fun _ => t.cells)) f

instance (t : Tromino) (blocked available f : Finset Cell) :
    Decidable (ConflictCheck t blocked available f) := by
  unfold ConflictCheck
  infer_instance

/-- The available cells are globally covered and every tile covering one of
them avoids the blocked cells. These hypotheses also apply to residual tilings. -/
theorem conflict_excludes {t : Tromino} {global : Set Cell} {completed : Set (Finset Cell)}
    (h : t.IsFootprintTiling global completed) {blocked available f : Finset Cell}
    (availableInside : ∀ c ∈ available, c ∈ global)
    (avoids : ∀ g ∈ completed, ∀ c ∈ available, c ∈ g → Disjoint g blocked)
    (checked : ConflictCheck t blocked available f) : f ∉ completed := by
  intro hf
  obtain ⟨c,hc,notCovered,checked⟩ := checked
  obtain ⟨g,⟨hg,hgc⟩,_⟩ := h.uniqueCover c (availableInside c hc)
  obtain ⟨p,rfl⟩ := (h.tilesInside g hg).1
  have candidate := (TrominoAssignment.mem_coveringPlacementList_iff t c p).mpr
    ((TrominoAssignment.mem_coveringPlacements_iff t c p).mpr hgc)
  rcases checked p candidate with blocked | overlap
  · exact blocked (avoids _ hg c hc hgc)
  · obtain ⟨d,hd,hdf⟩ := Finset.not_disjoint_iff.mp overlap
    have eq := (h.partial (Set.Subset.refl completed)).nonoverlap _ hg f hf d hd hdf
    exact notCovered (eq ▸ hgc)

/-- Every potential crossing is directly blocked or strands an available cell. -/
def GuardedCheck (t : Tromino) (core region blocked available : Finset Cell) : Prop :=
  ∀ c ∈ core, ∀ p ∈ TrominoAssignment.coveringPlacementList t c,
    p.cells (fun _ => t.cells) ⊆ region ∨
      ¬ Disjoint (p.cells (fun _ => t.cells)) blocked ∨
        ConflictCheck t blocked available (p.cells (fun _ => t.cells))

instance (t : Tromino) (core region blocked available : Finset Cell) :
    Decidable (GuardedCheck t core region blocked available) := by
  unfold GuardedCheck
  infer_instance

theorem containment_of_guarded {t : Tromino} {global : Set Cell} {completed : Set (Finset Cell)}
    (h : t.IsFootprintTiling global completed) {core region blocked available f : Finset Cell}
    (availableInside : ∀ c ∈ available, c ∈ global)
    (availableAvoids : ∀ g ∈ completed, ∀ c ∈ available, c ∈ g → Disjoint g blocked)
    (checked : GuardedCheck t core region blocked available)
    (hf : f ∈ completed) (avoids : Disjoint f blocked) {c : Cell} (covers : c ∈ f) (inside : c ∈ core) :
    f ⊆ region := by
  obtain ⟨p,rfl⟩ := (h.tilesInside f hf).1
  have candidate := (TrominoAssignment.mem_coveringPlacementList_iff t c p).mpr
    ((TrominoAssignment.mem_coveringPlacements_iff t c p).mpr covers)
  rcases checked c inside p candidate with contained | blocked | conflict
  · exact contained
  · exact False.elim (blocked avoids)
  · exact False.elim (conflict_excludes h availableInside availableAvoids conflict hf)

end LeanTrominoes.CompletionBarrier
