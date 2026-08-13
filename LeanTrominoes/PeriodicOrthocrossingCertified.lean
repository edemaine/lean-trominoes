/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingHorizontalUnique
import LeanTrominoes.PeriodicOrthocrossingVerticalUnique

/-!
# Certified periodic orthocrossing drawing

The horizontal and vertical private-lane arguments combine to rule out every
common interior point between distinct parallel segment occurrences.  With
the separately proved orthogonality of the construction, this supplies the
global orthocrossing certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every pair of parallel constructed segment occurrences with a common
interior point has the same indexed occurrence key. -/
theorem drawing_hasUniqueParallelInteriors
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    HasUniqueParallelInteriors (drawing graph) := by
  intro first firstMem second secondMem
    firstTranslate secondTranslate point
    firstContains secondContains parallel
  rcases parallel with
    ⟨firstHorizontal, secondHorizontal⟩ |
      ⟨firstVertical, secondVertical⟩
  · exact drawing_hasUniqueHorizontalInteriors
      wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate point
      firstContains secondContains
      firstHorizontal secondHorizontal
  · exact drawing_hasUniqueVerticalInteriors
      wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate point
      firstContains secondContains
      firstVertical secondVertical

/-- The linear-grid construction is a proper periodic orthocrossing drawing
for every well-formed local graph of maximum degree three. -/
theorem drawing_isOrthocrossing
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    (drawing graph).IsOrthocrossing :=
  isOrthocrossing_of_isOrthogonal_of_uniqueParallelInteriors
    (drawing_isOrthogonal wellFormed isLocal degree)
    (drawing_hasUniqueParallelInteriors wellFormed degree isLocal)

end PeriodicOrthocrossing
end LeanTrominoes
