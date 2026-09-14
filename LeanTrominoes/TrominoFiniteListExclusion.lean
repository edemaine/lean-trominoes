/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoFiniteExclusion

/-! # Exclusion certificates checked with ordered cell lists

Filtering preserves list order, so the checker compares child lists directly
instead of repeatedly deciding equality of large finite sets. Soundness uses
the same exhaustive branching over every tile covering the chosen pivot.
-/

namespace LeanTrominoes.TrominoFiniteListExclusion

structure Node where
  cells : List Cell
  pivot : Cell
  children : List Nat

def Node.region (node : Node) : Finset Cell := node.cells.toFinset

def ValidStep (t : Tromino) (node : Node) (later : List Node) : Prop :=
  node.pivot ∈ node.cells ∧ ∀ p ∈ TrominoAssignment.coveringPlacementList t node.pivot,
    (∀ c ∈ p.cells (fun _ => t.cells), c ∈ node.cells) →
      ∃ j ∈ node.children, ∃ child ∈ later[j]?,
        node.cells.filter (fun c => c ∉ p.cells (fun _ => t.cells)) = child.cells

instance (t : Tromino) (node : Node) (later : List Node) : Decidable (ValidStep t node later) := by
  unfold ValidStep
  infer_instance

def check (t : Tromino) : List Node → Bool
  | [] => true
  | node :: later => decide (ValidStep t node later) && check t later

theorem region_filter (node : Node) (tile : Finset Cell) :
    (node.cells.filter (fun c => c ∉ tile)).toFinset = node.region \ tile := by
  ext c
  simp [Node.region]

theorem check_sound (t : Tromino) (certificate : List Node) (valid : check t certificate = true) :
    ∀ node ∈ certificate, ¬ t.Tileable (node.region : Set Cell) := by
  induction certificate with
  | nil => simp
  | cons first later ih =>
    have checked : ValidStep t first later ∧ check t later = true := by
      simpa only [check,Bool.and_eq_true,decide_eq_true_eq] using valid
    intro node member
    rcases List.mem_cons.mp member with rfl | member
    · apply TrominoFiniteExclusion.not_tileable_at_cell t node.region node.pivot
        (List.mem_toFinset.mpr checked.1.1)
      intro p covers inside
      have candidate := (TrominoAssignment.mem_coveringPlacementList_iff t node.pivot p).mpr
        ((TrominoAssignment.mem_coveringPlacements_iff t node.pivot p).mpr covers)
      have inList : ∀ c ∈ p.cells (fun _ => t.cells), c ∈ node.cells :=
        fun c hc => List.mem_toFinset.mp (inside hc)
      obtain ⟨j,_,child,hchild,eq⟩ := checked.1.2 p candidate inList
      have regions : node.region \ p.cells (fun _ => t.cells) = child.region := by
        rw [← region_filter,eq]
        rfl
      rw [regions]
      exact ih checked.2 child (List.mem_of_getElem? hchild)
    · exact ih checked.2 node member

end LeanTrominoes.TrominoFiniteListExclusion
