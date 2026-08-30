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

end AxisDirection
end LeanTrominoes
