/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.CompletionBarrier
import LeanTrominoes.Tiling.Completion.TrominoCompletionTranslation

/-! # Translating a finite avoidance certificate -/
namespace LeanTrominoes.CompletionBarrier

theorem containment_of_avoidance_at {t : Tromino} {core region blocked f : Finset Cell}
    (v : Cell) (checked : AvoidanceCheck t core region blocked) (shape : t.IsFootprint f)
    (avoids : Disjoint f (blocked.image (Cell.add v))) {c : Cell}
    (covers : Cell.add v c ∈ f) (inside : c ∈ core) :
    f ⊆ region.image (Cell.add v) := by
  let inv := fun d => Cell.sub d v
  have cancel (d : Cell) : Cell.add v (inv d)=d := by
    apply Prod.ext <;> dsimp [inv,Cell.add,Cell.sub] <;> omega
  have cancel' (d : Cell) : inv (Cell.add v d)=d := by
    apply Prod.ext <;> dsimp [inv,Cell.add,Cell.sub] <;> omega
  have localShape : t.IsFootprint (f.image inv) := by
    obtain ⟨p,hp⟩ := shape
    refine ⟨p.shift (Cell.sub (0,0) v),?_⟩
    rw [← hp]
    simp only [Placement.cells,Placement.shift,Finset.image_image]
    apply Finset.image_congr
    intro d hd
    apply Prod.ext <;> dsimp [inv,Cell.add,Cell.sub] <;> omega
  have localAvoids : Disjoint (f.image inv) blocked := by
    apply Finset.disjoint_left.mpr
    intro d hd hb
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
    exact Finset.disjoint_left.mp avoids he (Finset.mem_image.mpr ⟨inv e,hb,cancel e⟩)
  have contained := containment_of_avoidance checked localShape localAvoids
    (Finset.mem_image.mpr ⟨Cell.add v c,covers,cancel' c⟩) inside
  intro d hd
  exact Finset.mem_image.mpr ⟨inv d,contained (Finset.mem_image.mpr ⟨d,hd,rfl⟩),cancel d⟩
end LeanTrominoes.CompletionBarrier
