/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPatternResidual
import LeanTrominoes.TrominoFiniteIndexedExclusion

namespace LeanTrominoes.CompletionPattern

def Pattern.rejectsIndexed (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteIndexedExclusion.Node) : Bool :=
  !decide (∀ q ∈ p.prefill, q.cells (fun _ => p.tromino.cells) ⊆ p.target outside) ||
    !decide (3 ∣ (p.residual outside).card) ||
    (TrominoFiniteIndexedExclusion.check p.tromino certificate &&
      decide (p.residual outside ∈ certificate.map TrominoFiniteIndexedExclusion.Node.region))

theorem Pattern.not_completable_of_rejectsIndexed (p : Pattern) (outside : Finset Cell)
    (certificate : List TrominoFiniteIndexedExclusion.Node)
    (rejected : p.rejectsIndexed outside certificate = true) : ¬ p.Completable outside := by
  intro completed
  have legal := ((p.tromino.completable_iff _ _).mp completed).1
  have inside : decide (∀ q ∈ p.prefill,
      q.cells (fun _ => p.tromino.cells) ⊆ p.target outside) = true := by
    simp only [decide_eq_true_eq]
    intro q hq
    exact (legal.tilesInside _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩)).2
  have area : decide (3 ∣ (p.residual outside).card) = true := by
    simpa only [decide_eq_true_eq] using p.area_dvd outside completed
  have checked : TrominoFiniteIndexedExclusion.check p.tromino certificate = true ∧
      p.residual outside ∈ certificate.map TrominoFiniteIndexedExclusion.Node.region := by
    unfold Pattern.rejectsIndexed at rejected
    rw [inside,area] at rejected
    simpa using rejected
  obtain ⟨node,member,eq⟩ := List.mem_map.mp checked.2
  have tiled := p.residual_tileable outside completed
  rw [← eq] at tiled
  exact TrominoFiniteIndexedExclusion.check_sound _ _ checked.1 node member tiled

end LeanTrominoes.CompletionPattern
