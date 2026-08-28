/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEqualityNormalization

/-! # Atom-word columns of normalized equality clauses -/

namespace LeanTrominoes
namespace PeriodicEquality

/-- The two normalized implication clauses of one equality link mention the
same endpoints in the same order, independently of polarity. -/
theorem normalizedClause_pair_atomWords
    {Variable : Type*}
    (word : Variable → List Bool)
    (link : NormalizedLink Variable) :
    (([link].product [true, false]).map normalizedClause).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      [word link.first, word link.second,
        word link.first, word link.second] := by
  simp [List.product, normalizedClause]

/-- Consequently a normalized equality family flattens to one fixed
four-word endpoint block per link, in link-presentation order. -/
theorem normalizedClauses_atomWords
    {Variable : Type*}
    (word : Variable → List Bool)
    (links : List (NormalizedLink Variable)) :
    ((links.product [true, false]).map normalizedClause).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      links.flatMap fun link =>
        [word link.first, word link.second,
          word link.first, word link.second] := by
  unfold List.product
  rw [List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro link _linkMember
  simp [normalizedClause]

end PeriodicEquality
end LeanTrominoes
