/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasureRightLocalization

/-! # Normalization across an out-and-back route excursion -/

namespace LeanTrominoes
namespace AxisDirection

open PeriodicOrthocrossing

/-- If the unit subdivision of an orthogonal route consists of a leading
path, a duplicate-free out-and-back excursion, and a remaining suffix, then
normalization cancels the excursion. -/
theorem normalizeOrthogonalPolyline_of_unitSubdivide_outAndBack
    (route leading path rest : List Cell)
    (routeNonempty : route ≠ [])
    (routeOrthogonal : OrthogonalPolyline route)
    (pathNonempty : path ≠ [])
    (subdivision :
      unitSubdividePolyline route =
        leading ++ path ++ path.reverse.tail ++ rest)
    (pathRestNodup : (path ++ rest).Nodup)
    (resultNodup :
      (leading ++ path.head pathNonempty :: rest).Nodup) :
    normalizeOrthogonalPolyline route =
      leading ++ path.head pathNonempty :: rest := by
  rw [normalizeOrthogonalPolyline_eq_listLoopErase
    routeNonempty routeOrthogonal, subdivision]
  exact Computability.listLoopErase_append_outAndBack_append
    leading path rest pathNonempty pathRestNodup resultNodup

/-- If the unit subdivisions on the two sides of an endpoint join traverse
the same terminal path in opposite directions, normalization cancels that
overlap and joins the preceding and following unit paths. -/
theorem normalizeOrthogonalPolyline_joinAtEndpoint_of_unit_outAndBack
    (first second leading path rest : List Cell)
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (pathNonempty : path ≠ [])
    (firstSubdivision :
      unitSubdividePolyline first = leading ++ path)
    (secondSubdivision :
      unitSubdividePolyline second = path.reverse ++ rest)
    (pathRestNodup : (path ++ rest).Nodup)
    (resultNodup :
      (leading ++ path.head pathNonempty :: rest).Nodup) :
    normalizeOrthogonalPolyline (joinAtEndpoint first second) =
      leading ++ path.head pathNonempty :: rest := by
  have pathReverseNonempty : path.reverse ≠ [] := by
    simpa using pathNonempty
  let boundary := path.getLast pathNonempty
  have pathLast : path.getLast? = some boundary :=
    List.getLast?_eq_some_getLast pathNonempty
  have firstLast :
      first.getLast? = some boundary := by
    rw [← unitSubdividePolyline_getLast?
        firstNonempty firstOrthogonal,
      firstSubdivision,
      List.getLast?_append_of_ne_nil leading pathNonempty,
      pathLast]
  have secondHead :
      second.head? = some boundary := by
    rw [← unitSubdividePolyline_head? secondNonempty,
      secondSubdivision,
      List.head?_append_of_ne_nil path.reverse pathReverseNonempty,
      List.head?_reverse, pathLast]
  have joinedOrthogonal :
      OrthogonalPolyline (joinAtEndpoint first second) :=
    firstOrthogonal.joinAtEndpoint secondOrthogonal
      firstLast secondHead
  have joinedNonempty : joinAtEndpoint first second ≠ [] := by
    intro empty
    unfold joinAtEndpoint at empty
    exact firstNonempty (List.append_eq_nil_iff.mp empty).1
  apply normalizeOrthogonalPolyline_of_unitSubdivide_outAndBack
    (joinAtEndpoint first second) leading path rest
    joinedNonempty joinedOrthogonal pathNonempty
  · rw [unitSubdividePolyline_joinAtEndpoint
      firstNonempty firstLast secondHead,
      firstSubdivision, secondSubdivision]
    unfold joinAtEndpoint
    rw [List.tail_append_of_ne_nil pathReverseNonempty]
    simp [List.append_assoc]
  · exact pathRestNodup
  · exact resultNodup

end AxisDirection
end LeanTrominoes
