/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTime

/-! # Semantics of joining well-delimited route streams -/

namespace LeanTrominoes.DelimitedRouteJoin

def delimited (directions : List AxisDirection) : List Token :=
  directions.map .direction ++ [.routeEnd]

theorem joinedAux_prefix_delimited
    (directions : List AxisDirection) (prefixes suffixes : List Token) :
    joinedAux .prefix (delimited directions ++ prefixes) suffixes =
      directions.map .direction ++ joinedAux .suffix prefixes suffixes := by
  induction directions with
  | nil => simp [delimited, joinedAux, resultAux]
  | cons direction directions induction =>
      rw [show delimited (direction :: directions) ++ prefixes =
        .direction direction :: (delimited directions ++ prefixes) by
          simp [delimited]]
      simp only [joinedAux, resultAux]
      rw [List.map_cons, List.cons_append]
      congr 1

theorem joinedAux_suffix_delimited
    (directions : List AxisDirection) (prefixes suffixes : List Token) :
    joinedAux .suffix prefixes (delimited directions ++ suffixes) =
      directions.map .direction ++ .routeEnd ::
        joinedAux .prefix prefixes suffixes := by
  induction directions with
  | nil => simp [delimited, joinedAux, resultAux]
  | cons direction directions induction =>
      rw [show delimited (direction :: directions) ++ suffixes =
        .direction direction :: (delimited directions ++ suffixes) by
          simp [delimited]]
      simp only [joinedAux, resultAux]
      rw [List.map_cons, List.cons_append]
      congr 1

/-- Corresponding complete route blocks are concatenated pointwise, retaining
one delimiter after the joined direction word. -/
theorem joined_delimited_append
    (prefixDirections suffixDirections : List AxisDirection)
    (prefixes suffixes : List Token) :
    joined (delimited prefixDirections ++ prefixes)
        (delimited suffixDirections ++ suffixes) =
      delimited (prefixDirections ++ suffixDirections) ++
        joined prefixes suffixes := by
  rw [joined, joinedAux_prefix_delimited,
    joinedAux_suffix_delimited]
  simp [delimited, List.map_append, joined]

/-- Pointwise joining distributes over equally long families of complete
route blocks. -/
theorem joined_flatMap_delimited
    (routes : List (List AxisDirection × List AxisDirection)) :
    joined
        (routes.flatMap fun route => delimited route.1)
        (routes.flatMap fun route => delimited route.2) =
      routes.flatMap fun route => delimited (route.1 ++ route.2) := by
  induction routes with
  | nil => simp [joined, joinedAux, resultAux]
  | cons route routes induction =>
      rcases route with ⟨prefixDirections, suffixDirections⟩
      simp only [List.flatMap_cons]
      rw [joined_delimited_append, induction]

end LeanTrominoes.DelimitedRouteJoin
