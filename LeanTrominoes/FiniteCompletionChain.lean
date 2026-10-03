/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoCompletion
import Mathlib.Order.Monotone.Basic

/-! # Increasing finite partial tilings exhaust the plane -/
namespace LeanTrominoes.Tromino

theorem completable_of_increasing_covers (t : Tromino) (chain : Nat → Finset (Finset Cell))
    (packing : ∀ n, t.IsPartialTiling Set.univ (chain n : Set (Finset Cell)))
    (mono : Monotone chain)
    (covers : ∀ c : Cell, ∃ n, ∃ f∈chain n, c∈f) :
    t.Completable Set.univ (chain 0 : Set (Finset Cell)) := by
  let completed : Set (Finset Cell) := {f | ∃ n, f∈chain n}
  refine ⟨completed,⟨?_,?_⟩,?_⟩
  · rintro f ⟨n,hf⟩
    exact (packing n).tilesInside f hf
  · intro c _
    obtain ⟨n,f,hf,hc⟩ := covers c
    refine ⟨f,⟨⟨n,hf⟩,hc⟩,?_⟩
    rintro g ⟨⟨m,hg⟩,hgc⟩
    exact (packing (max m n)).nonoverlap g (mono (Nat.le_max_left _ _) hg)
      f (mono (Nat.le_max_right _ _) hf) c hgc hc
  · intro f hf; exact ⟨0,hf⟩

end LeanTrominoes.Tromino
