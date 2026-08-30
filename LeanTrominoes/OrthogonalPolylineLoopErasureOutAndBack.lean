/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
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

/-- At the direction-word boundary, cancelling an out-and-back join removes
the overlap's edge count from the end of the first word and the beginning of
the second word. -/
theorem unitSubdivisionDirections_normalize_joinAtEndpoint_of_unit_outAndBack
    (first second leading path rest : List Cell)
    (firstNonempty : first ≠ [])
    (secondNonempty : second ≠ [])
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (pathNonempty : path ≠ [])
    (pathUnitSteps : path.IsChain IsUnitAxisStep)
    (firstSubdivision :
      unitSubdividePolyline first = leading ++ path)
    (secondSubdivision :
      unitSubdividePolyline second = path.reverse ++ rest)
    (pathRestNodup : (path ++ rest).Nodup)
    (resultNodup :
      (leading ++ path.head pathNonempty :: rest).Nodup) :
    Gadget.unitSubdivisionDirections
        (normalizeOrthogonalPolyline (joinAtEndpoint first second)) =
      (Gadget.unitSubdivisionDirections first).take
          ((Gadget.unitSubdivisionDirections first).length -
            (path.length - 1)) ++
        (Gadget.unitSubdivisionDirections second).drop
          (path.length - 1) := by
  let overlapHead := path.head pathNonempty
  let prefixRoute := leading ++ [overlapHead]
  let suffixRoute := overlapHead :: rest
  have pathHead : path.head? = some overlapHead :=
    List.head?_eq_some_head pathNonempty
  have prefixNonempty : prefixRoute ≠ [] := by simp [prefixRoute]
  have prefixLast : prefixRoute.getLast? = some overlapHead := by
    simp [prefixRoute]
  have suffixHead : suffixRoute.head? = some overlapHead := by
    rfl
  have pathReverseNonempty : path.reverse ≠ [] := by
    simpa using pathNonempty
  have pathReverseLast : path.reverse.getLast? = some overlapHead := by
    rw [List.getLast?_reverse, pathHead]
  have firstPoints :
      leading ++ path = joinAtEndpoint prefixRoute path := by
    unfold prefixRoute joinAtEndpoint
    cases path with
    | nil => exact (pathNonempty rfl).elim
    | cons head tail => simp [overlapHead]
  have secondPoints :
      path.reverse ++ rest = joinAtEndpoint path.reverse suffixRoute := by
    unfold suffixRoute joinAtEndpoint
    simp
  have resultPoints :
      leading ++ overlapHead :: rest =
        joinAtEndpoint prefixRoute suffixRoute := by
    unfold prefixRoute suffixRoute joinAtEndpoint
    simp
  have firstDirections :
      Gadget.unitSubdivisionDirections first =
        Gadget.unitSubdivisionDirections prefixRoute ++
          Gadget.unitSubdivisionDirections path := by
    rw [← Gadget.unitSubdivisionDirections_unitSubdividePolyline
        first firstOrthogonal,
      firstSubdivision, firstPoints,
      Gadget.unitSubdivisionDirections_joinAtEndpoint
        prefixNonempty (by rw [prefixLast, pathHead])]
  have secondDirections :
      Gadget.unitSubdivisionDirections second =
        Gadget.unitSubdivisionDirections path.reverse ++
          Gadget.unitSubdivisionDirections suffixRoute := by
    rw [← Gadget.unitSubdivisionDirections_unitSubdividePolyline
        second secondOrthogonal,
      secondSubdivision, secondPoints,
      Gadget.unitSubdivisionDirections_joinAtEndpoint
        pathReverseNonempty (by rw [pathReverseLast, suffixHead])]
  have pathDirectionsLength :
      (Gadget.unitSubdivisionDirections path).length =
        path.length - 1 := by
    obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil pathNonempty
    rw [Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
      (head :: tail) pathUnitSteps]
    simp
  have pathReverseUnitSteps :
      path.reverse.IsChain IsUnitAxisStep := by
    rw [List.isChain_reverse]
    exact pathUnitSteps.imp fun _ _ unit => unit.symm
  have pathReverseDirectionsLength :
      (Gadget.unitSubdivisionDirections path.reverse).length =
        path.length - 1 := by
    rw [Gadget.unitSubdivisionDirections_eq_routeStepDirections_of_unitSteps
      path.reverse pathReverseUnitSteps]
    obtain ⟨reverseHead, reverseTail, reverseEq⟩ :=
      List.exists_cons_of_ne_nil pathReverseNonempty
    rw [reverseEq, Gadget.routeStepDirections_length]
    have lengthEq := congrArg List.length reverseEq
    simp only [List.length_reverse, List.length_cons] at lengthEq
    omega
  have normalized :=
    normalizeOrthogonalPolyline_joinAtEndpoint_of_unit_outAndBack
      first second leading path rest firstNonempty secondNonempty
      firstOrthogonal secondOrthogonal pathNonempty
      firstSubdivision secondSubdivision pathRestNodup resultNodup
  rw [normalized, resultPoints,
    Gadget.unitSubdivisionDirections_joinAtEndpoint
      prefixNonempty (by rw [prefixLast, suffixHead]),
    firstDirections, secondDirections]
  simp [pathDirectionsLength, pathReverseDirectionsLength]

end AxisDirection
end LeanTrominoes
