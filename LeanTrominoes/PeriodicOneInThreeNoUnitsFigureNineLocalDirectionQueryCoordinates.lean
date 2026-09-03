/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionCompiler

/-! # Extensionality of finite Figure 9 local direction queries -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- A finite local query is uniquely determined by its profile and the
clause/literal presentation coordinates of its selected incidence. -/
theorem LocalDirectionQuery.eq_of_profile_and_coordinates
    (first second : LocalDirectionQuery)
    (profileEq : first.1 = second.1)
    (clauseEq :
      ((templateDrawingOfClauseProfile first.1).incidenceAt
        first.2).clauseIndex =
      ((templateDrawingOfClauseProfile second.1).incidenceAt
        second.2).clauseIndex)
    (literalEq :
      ((templateDrawingOfClauseProfile first.1).incidenceAt
        first.2).literalIndex =
      ((templateDrawingOfClauseProfile second.1).incidenceAt
        second.2).literalIndex) :
    first = second := by
  rcases first with ⟨firstProfile, firstIndex⟩
  rcases second with ⟨secondProfile, secondIndex⟩
  dsimp only at profileEq
  subst secondProfile
  have indexEq : firstIndex = secondIndex := by
    by_contra different
    rcases
        (templateDrawingOfClauseProfile firstProfile).incidenceCoordinates_ne_of_ne
          different with clauseNe | literalNe
    · exact clauseNe clauseEq
    · exact literalNe literalEq
  subst secondIndex
  rfl

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
