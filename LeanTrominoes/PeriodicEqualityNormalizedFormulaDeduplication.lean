/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupDisjointBlocks
import LeanTrominoes.PeriodicEqualityNormalization

/-! # Exact deduplication of normalized equality formulas -/

namespace LeanTrominoes
namespace PeriodicEquality

open PlanarThreeSAT

/-- Last-occurrence deduplication of normalized equality clauses can be
performed on normalized links before expanding each retained link into its
two implication clauses, without changing presentation order. -/
theorem dedup_normalizedFormulaClauses_eq
    {Source Target : Type*} [DecidableEq Target]
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source)) :
    (normalizedFormulaClauses normalize links).dedup =
      (((links.map (normalizeLink normalize)).dedup).product
        [true, false]).map normalizedClause := by
  rw [normalizedFormulaClauses_eq]
  simp only [List.product, List.map_flatMap]
  change
    (((links.map (normalizeLink normalize)).flatMap fun link =>
      [true, false].map fun polarity =>
        normalizedClause (link, polarity))).dedup = _
  rw [List.dedup_flatMap_blocks]
  · rfl
  · intro link
    exact (by decide : ([true, false] : List Bool).Nodup).map
      (fun first second equal =>
        congrArg Prod.snd (normalizedClause_injective equal))
  · intro first second linksNe
    rw [List.disjoint_left]
    intro clause firstMember secondMember
    rcases List.mem_map.mp firstMember with
      ⟨firstPolarity, _firstPolarityMember, firstEq⟩
    rcases List.mem_map.mp secondMember with
      ⟨secondPolarity, _secondPolarityMember, secondEq⟩
    apply linksNe
    exact congrArg (fun input => input.1)
      (normalizedClause_injective (firstEq.trans secondEq.symm))

end PeriodicEquality
end LeanTrominoes
