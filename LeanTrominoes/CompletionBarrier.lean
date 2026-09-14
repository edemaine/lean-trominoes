/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletionRestriction
import LeanTrominoes.ComputableSearch

/-! # Finite checks that preplaced tiles block crossings of subbrick boundaries -/

namespace LeanTrominoes.CompletionBarrier

def Blocked (t : Tromino) (prefill : Finset (Placement Unit)) (f : Finset Cell) : Prop :=
  ∃ q ∈ prefill, f ≠ q.cells (fun _ => t.cells) ∧
    ¬ Disjoint f (q.cells (fun _ => t.cells))

instance (t : Tromino) (prefill : Finset (Placement Unit)) (f : Finset Cell) :
    Decidable (Blocked t prefill f) := by unfold Blocked; infer_instance

def Check (t : Tromino) (region boundary : Finset Cell)
    (prefill : Finset (Placement Unit)) : Prop :=
  ∀ c ∈ region \ boundary, ∀ p ∈ TrominoAssignment.coveringPlacementList t c,
    p.cells (fun _ => t.cells) ⊆ region ∨ Blocked t prefill (p.cells (fun _ => t.cells))

instance (t : Tromino) (region boundary : Finset Cell)
    (prefill : Finset (Placement Unit)) : Decidable (Check t region boundary prefill) := by
  unfold Check
  infer_instance

theorem no_crossing {t : Tromino} {global : Set Cell} {completed : Set (Finset Cell)}
    (h : t.IsFootprintTiling global completed) (region boundary : Finset Cell)
    (prefill : Finset (Placement Unit))
    (retained : ∀ q ∈ prefill, q.cells (fun _ => t.cells) ∈ completed)
    (checked : Check t region boundary prefill) :
    ∀ f ∈ completed, ∀ c ∈ f, c ∈ region \ boundary → f ⊆ region := by
  intro f hf c hfc hc
  obtain ⟨p,rfl⟩ := (h.tilesInside f hf).1
  have candidate := (TrominoAssignment.mem_coveringPlacementList_iff t c p).mpr
    ((TrominoAssignment.mem_coveringPlacements_iff t c p).mpr hfc)
  rcases checked c hc p candidate with inside | blocked
  · exact inside
  · obtain ⟨q,hq,neq,overlap⟩ := blocked
    obtain ⟨d,hd,hdq⟩ := Finset.not_disjoint_iff.mp overlap
    exact False.elim (neq ((h.partial (Set.Subset.refl completed)).nonoverlap
      _ hf _ (retained q hq) d hd hdq))

/-- For residual tilings, occupied cells alone suffice to block a placement. -/
def AvoidanceCheck (t : Tromino) (core region filled : Finset Cell) : Prop :=
  ∀ c ∈ core, ∀ p ∈ TrominoAssignment.coveringPlacementList t c,
    p.cells (fun _ => t.cells) ⊆ region ∨ ¬ Disjoint (p.cells (fun _ => t.cells)) filled

instance (t : Tromino) (core region filled : Finset Cell) :
    Decidable (AvoidanceCheck t core region filled) := by
  unfold AvoidanceCheck
  infer_instance

theorem containment_of_avoidance {t : Tromino} {core region filled f : Finset Cell}
    (checked : AvoidanceCheck t core region filled) (shape : t.IsFootprint f)
    (avoids : Disjoint f filled) {c : Cell} (covers : c ∈ f) (inside : c ∈ core) :
    f ⊆ region := by
  obtain ⟨p,rfl⟩ := shape
  have candidate := (TrominoAssignment.mem_coveringPlacementList_iff t c p).mpr
    ((TrominoAssignment.mem_coveringPlacements_iff t c p).mpr covers)
  exact (checked c inside p candidate).resolve_right (fun blocked => blocked avoids)

end LeanTrominoes.CompletionBarrier
