/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPatternArea

namespace LeanTrominoes.CompletionPattern

def Pattern.fixedRegion (p : Pattern) : Finset Cell :=
  p.prefill.biUnion (Placement.cells (fun _ => p.tromino.cells))

theorem Pattern.completable_of_residual_solution (p : Pattern) (outside : Finset Cell)
    (solution : Finset (Placement Unit))
    (fixed : IsFiniteTiling (fun _ => p.tromino.cells) p.fixedRegion p.prefill)
    (inside : ∀ q ∈ p.prefill, q.cells (fun _ => p.tromino.cells) ⊆ p.target outside)
    (tiled : IsFiniteTiling (fun _ => p.tromino.cells) (p.residual outside) solution) :
    p.Completable outside := by
  have fixedCompletion := p.tromino.completable_of_finiteTiling _ _ _ fixed
    (Finset.Subset.refl p.prefill)
  have legal := ((p.tromino.completable_iff _ _).mp fixedCompletion).1
  have residualCompletion := p.tromino.completable_of_finiteTiling _ ∅ _ tiled
    (Finset.empty_subset solution)
  have residualTiled : p.tromino.Tileable (p.residual outside : Set Cell) := by
    apply (p.tromino.completable_empty _).mp
    simpa [Tromino.finiteFootprints] using residualCompletion
  apply (p.tromino.completable_iff _ _).mpr
  refine ⟨⟨?_,legal.nonoverlap⟩,?_⟩
  · intro f hf
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hf
    exact ⟨⟨q,rfl⟩,inside q hq⟩
  · have cells : (p.target outside : Set Cell) \
        Tromino.occupied (p.tromino.finiteFootprints p.prefill : Set (Finset Cell)) =
        (p.residual outside : Set Cell) := by
      ext c
      simp [Pattern.residual,Tromino.occupied,Tromino.finiteFootprints]
    rwa [cells]

end LeanTrominoes.CompletionPattern
