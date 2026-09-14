/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletion

/-! # Assembling completions on a partition of the target

The partition may depend on connector states: shared boundary cells are
assigned to exactly one neighboring piece before applying this theorem.
-/

namespace LeanTrominoes.Tromino

theorem IsFootprintTiling.assemble {ι : Type*} {t : Tromino}
    {regions : ι → Set Cell} {tiles : ι → Set (Finset Cell)}
    (localTilings : ∀ i, t.IsFootprintTiling (regions i) (tiles i))
    (separate : ∀ i j c, c ∈ regions i → c ∈ regions j → i = j) :
    t.IsFootprintTiling {c | ∃ i, c ∈ regions i} {f | ∃ i, f ∈ tiles i} := by
  constructor
  · rintro f ⟨i,hi⟩
    exact ⟨(localTilings i).tilesInside f hi |>.1,
      fun c hc => ⟨i,((localTilings i).tilesInside f hi).2 c hc⟩⟩
  · rintro c ⟨i,hi⟩
    obtain ⟨f,⟨hf,hfc⟩,unique⟩ := (localTilings i).uniqueCover c hi
    refine ⟨f,⟨⟨i,hf⟩,hfc⟩,?_⟩
    rintro g ⟨⟨j,hj⟩,hgc⟩
    have eq := separate j i c (((localTilings j).tilesInside g hj).2 c hgc) hi
    subst j
    exact unique g ⟨hj,hgc⟩

theorem completable_assemble {ι : Type*} {t : Tromino}
    {regions : ι → Set Cell} {prescribed : ι → Set (Finset Cell)}
    (localCompletions : ∀ i, t.Completable (regions i) (prescribed i))
    (separate : ∀ i j c, c ∈ regions i → c ∈ regions j → i = j) :
    t.Completable {c | ∃ i, c ∈ regions i} {f | ∃ i, f ∈ prescribed i} := by
  classical
  choose tiles tiled retained using localCompletions
  refine ⟨{f | ∃ i, f ∈ tiles i},IsFootprintTiling.assemble tiled separate,?_⟩
  rintro f ⟨i,hi⟩
  exact ⟨i,retained i hi⟩

end LeanTrominoes.Tromino
