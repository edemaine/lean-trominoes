/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletion
import LeanTrominoes.ComputableSearch

/-! # Finite exclusion certificates with shared subproblems

Each entry names a region and a cell. Every possible tile covering that cell
must leave a region already excluded by a later entry. Leaves have no legal
covering tile. The certificate checker does not trust the search that found it.
-/

namespace LeanTrominoes.TrominoFiniteExclusion

theorem not_tileable_at_cell (t : Tromino) (region : Finset Cell) (c : Cell)
    (inside : c ∈ region)
    (blocked : ∀ p : Placement Unit, c ∈ p.cells (fun _ => t.cells) →
      p.cells (fun _ => t.cells) ⊆ region →
      ¬ t.Tileable ((region \ p.cells (fun _ => t.cells) : Finset Cell) : Set Cell)) :
    ¬ t.Tileable (region : Set Cell) := by
  intro tiled
  obtain ⟨footprints,h⟩ := (t.tileable_iff_exists_footprintTiling _).mp tiled
  obtain ⟨f,⟨hf,hfc⟩,_⟩ := h.uniqueCover c inside
  obtain ⟨p,rfl⟩ := (h.tilesInside f hf).1
  have rest := h.remove (Set.singleton_subset_iff.mpr hf)
  have tiledRest := (t.tileable_iff_exists_footprintTiling _).mpr ⟨_,rest⟩
  have eq : (region : Set Cell) \ Tromino.occupied {p.cells (fun _ => t.cells)} =
      ((region \ p.cells (fun _ => t.cells) : Finset Cell) : Set Cell) := by
    ext x
    simp [Tromino.occupied]
  rw [eq] at tiledRest
  exact blocked p hfc (h.tilesInside _ hf).2 tiledRest

abbrev Node := Finset Cell × Cell

def ValidStep (t : Tromino) (node : Node) (later : List Node) : Prop :=
  node.2 ∈ node.1 ∧ ∀ p ∈ TrominoAssignment.coveringPlacementList t node.2,
    p.cells (fun _ => t.cells) ⊆ node.1 →
      node.1 \ p.cells (fun _ => t.cells) ∈ later.map Prod.fst

instance (t : Tromino) (node : Node) (later : List Node) : Decidable (ValidStep t node later) := by
  unfold ValidStep
  infer_instance

def check (t : Tromino) : List Node → Bool
  | [] => true
  | node :: later => decide (ValidStep t node later) && check t later

theorem check_sound (t : Tromino) (certificate : List Node) (valid : check t certificate = true) :
    ∀ node ∈ certificate, ¬ t.Tileable (node.1 : Set Cell) := by
  induction certificate with
  | nil => simp
  | cons first later ih =>
    have checked : ValidStep t first later ∧ check t later = true := by
      simpa only [check,Bool.and_eq_true,decide_eq_true_eq] using valid
    intro node member
    rcases List.mem_cons.mp member with rfl | member
    · apply not_tileable_at_cell t node.1 node.2 checked.1.1
      intro p covers inside
      have candidate := (TrominoAssignment.mem_coveringPlacementList_iff t node.2 p).mpr
        ((TrominoAssignment.mem_coveringPlacements_iff t node.2 p).mpr covers)
      obtain ⟨child,hchild,eq⟩ := List.mem_map.mp (checked.1.2 p candidate inside)
      rw [← eq]
      exact ih checked.2 child hchild
    · exact ih checked.2 node member

end LeanTrominoes.TrominoFiniteExclusion
