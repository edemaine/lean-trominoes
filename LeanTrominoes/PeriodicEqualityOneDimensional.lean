/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicEqualityNormalization

/-!
# One-dimensional normalized equality families

Anchor-normalizing an equality link leaves only the second endpoint's offset
relative to the first.  Hence a family of physical links whose endpoints
normalize to equal vertical shifts produces a one-dimensional periodic CNF.
-/

namespace LeanTrominoes
namespace PeriodicEquality

open PlanarThreeSAT

/-- A normalized equality clause is horizontal when its link's relative
vertical offset is zero. -/
theorem normalizedClause_isOneDimensional
    {Variable : Type*} (link : NormalizedLink Variable)
    (verticalZero : link.relativeOffset.2 = 0)
    (polarity : Bool) :
    ∀ literal ∈ normalizedClause (link, polarity),
      literal.offset.2 = 0 := by
  cases polarity <;> simp [normalizedClause, verticalZero]

/-- Equal vertical normalization shifts at every physical link endpoint
make the complete anchor-normalized equality family one dimensional. -/
theorem normalizedFormulaClauses_isOneDimensional
    {Source Target : Type*}
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source))
    (verticalEqual :
      ∀ link ∈ links,
        (normalize link.first).2.2 = (normalize link.second).2.2) :
    PeriodicCNF.IsOneDimensional
      ⟨normalizedFormulaClauses normalize links⟩ := by
  intro clause clauseMember literal literalMember
  rw [normalizedFormulaClauses_eq] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedLink, taggedLinkMember, rfl⟩
  rcases taggedLink with ⟨normalizedLink, polarity⟩
  have normalizedLinkMember :
      normalizedLink ∈ links.map (normalizeLink normalize) :=
    (List.mem_product.mp taggedLinkMember).1
  rcases List.mem_map.mp normalizedLinkMember with
    ⟨link, linkMember, rfl⟩
  apply normalizedClause_isOneDimensional
      (normalizeLink normalize link) ?_ polarity literal literalMember
  have equal := verticalEqual link linkMember
  simp [normalizeLink, Cell.sub, equal]

end PeriodicEquality
end LeanTrominoes
