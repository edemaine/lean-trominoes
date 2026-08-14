/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensional
import LeanTrominoes.PeriodicOneInThree

/-!
# One-dimensional exact-one conversion

Every Figure 9 literal is supported either at an original source-literal
offset or at the source clause's first-literal anchor.  Both locations are
horizontal when the source formula is one dimensional.
-/

namespace LeanTrominoes
namespace PeriodicOneInThree

/-- A Figure 9 literal supported by a horizontal source clause has zero
vertical offset. -/
theorem Supported.vertical_eq_zero
    {Variable : Type*}
    {source : PeriodicClause Variable}
    (horizontal : ∀ literal ∈ source, literal.offset.2 = 0)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    (supported : Supported source literal) :
    literal.offset.2 = 0 := by
  rcases supported with ⟨original, originalMember, offsetEqual⟩ |
      offsetEqual
  · simpa [offsetEqual] using horizontal original originalMember
  · cases source with
    | nil => simpa [anchor] using congrArg Prod.snd offsetEqual
    | cons first rest =>
        have firstVertical := horizontal first (by simp)
        simpa [anchor, offsetEqual] using firstVertical

/-- Figure 9's periodic exact-one conversion preserves the
one-dimensional fragment. -/
theorem formula_isOneDimensional
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (horizontal : source.IsOneDimensional) :
    (formula source).IsOneDimensional := by
  intro clause clauseMember literal literalMember
  simp only [formula, List.mem_flatMap] at clauseMember
  obtain ⟨taggedClause, taggedClauseMember, clauseMember⟩ := clauseMember
  exact Supported.vertical_eq_zero
    (horizontal taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember))
    (clauseClauses_supported taggedClause.2 taggedClause.1
      clause clauseMember literal literalMember)

end PeriodicOneInThree
end LeanTrominoes
