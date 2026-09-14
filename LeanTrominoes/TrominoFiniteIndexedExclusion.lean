/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoFiniteExclusion

namespace LeanTrominoes.TrominoFiniteIndexedExclusion

structure Node where
  region : Finset Cell
  pivot : Cell
  children : List Nat

def ValidStep (t : Tromino) (node : Node) (later : List Node) : Prop :=
  node.pivot ∈ node.region ∧ ∀ p ∈ TrominoAssignment.coveringPlacementList t node.pivot,
    p.cells (fun _ => t.cells) ⊆ node.region →
      ∃ j ∈ node.children, ∃ child, later[j]? = some child ∧
        node.region \ p.cells (fun _ => t.cells) = child.region

instance (t : Tromino) (node : Node) (later : List Node) : Decidable (ValidStep t node later) := by
  unfold ValidStep
  exact inferInstanceAs (Decidable (node.pivot ∈ node.region ∧
    ∀ p ∈ TrominoAssignment.coveringPlacementList t node.pivot,
      p.cells (fun _ => t.cells) ⊆ node.region →
        ∃ j ∈ node.children, ∃ child ∈ later[j]?,
          node.region \ p.cells (fun _ => t.cells) = child.region))

def check (t : Tromino) : List Node → Bool
  | [] => true
  | node :: later => decide (ValidStep t node later) && check t later

theorem check_sound (t : Tromino) (certificate : List Node) (valid : check t certificate = true) :
    ∀ node ∈ certificate, ¬ t.Tileable (node.region : Set Cell) := by
  induction certificate with
  | nil => simp
  | cons first later ih =>
    have checked : ValidStep t first later ∧ check t later = true := by
      simpa only [check,Bool.and_eq_true,decide_eq_true_eq] using valid
    intro node member
    rcases List.mem_cons.mp member with rfl | member
    · apply TrominoFiniteExclusion.not_tileable_at_cell t node.region node.pivot checked.1.1
      intro p covers inside
      have candidate := (TrominoAssignment.mem_coveringPlacementList_iff t node.pivot p).mpr
        ((TrominoAssignment.mem_coveringPlacements_iff t node.pivot p).mpr covers)
      obtain ⟨j,_,child,hchild,eq⟩ := checked.1.2 p candidate inside
      rw [eq]
      exact ih checked.2 child (List.mem_of_getElem? hchild)
    · exact ih checked.2 node member

end LeanTrominoes.TrominoFiniteIndexedExclusion
