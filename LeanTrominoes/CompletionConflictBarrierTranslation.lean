/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionConflictBarrier
import LeanTrominoes.TrominoCompletionTranslation

namespace LeanTrominoes.CompletionBarrier

set_option maxHeartbeats 2000000

private theorem cancel (v c : Cell) : Cell.add (Cell.sub (0,0) v) (Cell.add v c) = c := by
  apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega

private theorem cancel' (v c : Cell) : Cell.add v (Cell.add (Cell.sub (0,0) v) c) = c := by
  apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega

private theorem inverse_disjoint (v : Cell) (g blocked : Finset Cell)
    (h : Disjoint g (blocked.image (Cell.add v))) :
    Disjoint (g.image (Cell.add (Cell.sub (0,0) v))) blocked := by
  apply Finset.disjoint_left.mpr
  intro c hc hb
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
  exact Finset.disjoint_left.mp h hd (Finset.mem_image.mpr ⟨_,hb,cancel' v d⟩)

/-- A finite conflict certificate remains sound at any translate in an
arbitrary full or residual tiling. -/
theorem containment_of_guarded_at {t : Tromino} {global : Set Cell}
    {completed : Set (Finset Cell)} (h : t.IsFootprintTiling global completed)
    (v : Cell) {core region blocked available f : Finset Cell}
    (availableInside : ∀ c ∈ available, Cell.add v c ∈ global)
    (availableAvoids : ∀ g ∈ completed, ∀ c ∈ available, Cell.add v c ∈ g →
      Disjoint g (blocked.image (Cell.add v)))
    (checked : GuardedCheck t core region blocked available)
    (hf : f ∈ completed) (avoids : Disjoint f (blocked.image (Cell.add v)))
    {c : Cell} (covers : Cell.add v c ∈ f) (inside : c ∈ core) :
    f ⊆ region.image (Cell.add v) := by
  let inv := Cell.add (Cell.sub (0,0) v)
  have localTiling := h.translate (Cell.sub (0,0) v)
  have localInside : ∀ d ∈ available, d ∈ inv '' global := by
    intro d hd
    exact ⟨Cell.add v d,availableInside d hd,cancel v d⟩
  have localAvoids : ∀ g ∈ (fun g => g.image inv) '' completed,
      ∀ d ∈ available, d ∈ g → Disjoint g blocked := by
    rintro g ⟨original,hg,rfl⟩ d hd member
    obtain ⟨e,he,eq⟩ := Finset.mem_image.mp member
    have translated : Cell.add v d = e := by rw [← eq]; exact cancel' v e
    exact inverse_disjoint v original blocked (availableAvoids original hg d hd (translated ▸ he))
  have localCover : c ∈ f.image inv := Finset.mem_image.mpr ⟨Cell.add v c,covers,cancel v c⟩
  have contained := containment_of_guarded localTiling localInside localAvoids checked
    (show f.image inv ∈ (fun g => g.image inv) '' completed from ⟨f,hf,rfl⟩)
    (inverse_disjoint v f blocked avoids) localCover inside
  intro d hd
  exact Finset.mem_image.mpr ⟨inv d,contained (Finset.mem_image.mpr ⟨d,hd,rfl⟩),cancel' v d⟩

end LeanTrominoes.CompletionBarrier
