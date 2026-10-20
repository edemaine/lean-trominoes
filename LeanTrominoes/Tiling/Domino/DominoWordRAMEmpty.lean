/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMSizeBounds

/-! # Empty representative lists are accepted without lattice arithmetic -/
namespace LeanTrominoes.Domino.WordRAM

theorem empty_matching {d : ℕ} (B : BasisData 0 d) :
    BipartiteMatching.DenseWordRAM.predicate (SizeBounds.matchingInput B) := by
  classical
  refine ⟨Equiv.refl _,?_⟩
  intro l
  rw [BipartiteMatching.DenseSearch.mem_edgeBuckets]
  have equal : l=Fin.last (0*2^d) := by
    apply Fin.ext
    have small := l.isLt
    change l.val < 0*2^d+1 at small
    simp only [zero_mul,zero_add] at small
    simp only [Fin.val_last,zero_mul]
    omega
  change (l,l) ∈ PaddedGraph.edges B
  rw [equal]
  exact List.mem_cons.mpr (Or.inl rfl)

theorem empty_tileable {d : ℕ} (B : BasisData 0 d) (valid : B.Valid) :
    Tileable (B.chart valid).region :=
  (PaddedGraph.matching_iff_tileable B valid).mp (empty_matching B)

end LeanTrominoes.Domino.WordRAM
