/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRouteWord

/-! # Joining route pieces commutes with periodic translation -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem joinWord_translate (offset : Cell) (word : List (List Cell)) :
    joinWord (word.map (translatePolyline offset)) = translatePolyline offset (joinWord word) := by
  induction word with
  | nil => simp [joinWord,translatePolyline]
  | cons first rest ih =>
    cases rest with
    | nil => simp [joinWord]
    | cons next rest =>
      simp only [List.map_cons,joinWord] at ih ⊢
      rw [ih]
      simp [joinPolylines,translatePolyline,List.map_tail]

end LeanTrominoes.GridPolyline
