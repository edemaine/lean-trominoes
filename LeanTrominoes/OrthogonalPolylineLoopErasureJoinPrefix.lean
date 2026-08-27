/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureJoin

/-!
# Contact localization across a joined prefix

Strict separation of the first piece and boundary-only contact for the second
piece combine into boundary-only contact for their endpoint join.
-/

namespace LeanTrominoes
namespace AxisDirection

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A joined prefix meets a third route only at a specified boundary when
its first piece strictly avoids the third route and its second piece has only
that boundary contact. -/
theorem unitSubdividePolyline_only_common_of_join_left_strict
    {first second third : List Cell}
    {joinBoundary commonBoundary : Cell}
    (firstNonempty : first ≠ [])
    (firstLast : first.getLast? = some joinBoundary)
    (secondHead : second.head? = some joinBoundary)
    (firstOrthogonal : OrthogonalPolyline first)
    (thirdOrthogonal : OrthogonalPolyline third)
    (firstThirdStrict : RoutesStrictlyAvoidEachOther first third)
    (secondThirdOnlyCommon :
      ∀ point,
        point ∈ unitSubdividePolyline second →
        point ∈ unitSubdividePolyline third →
        point = commonBoundary) :
    ∀ point,
      point ∈ unitSubdividePolyline
        (joinAtEndpoint first second) →
      point ∈ unitSubdividePolyline third →
      point = commonBoundary := by
  have firstThirdDisjoint :
      List.Disjoint
        (unitSubdividePolyline first)
        (unitSubdividePolyline third) :=
    firstThirdStrict.unitSubdividePolyline_disjoint
      firstOrthogonal thirdOrthogonal
  intro point joinedMember thirdMember
  rw [unitSubdividePolyline_joinAtEndpoint
    firstNonempty firstLast secondHead] at joinedMember
  rcases mem_joinAtEndpoint joinedMember with
    firstMember | secondMember
  · exact (firstThirdDisjoint firstMember thirdMember).elim
  · exact secondThirdOnlyCommon point secondMember thirdMember

end AxisDirection
end LeanTrominoes
