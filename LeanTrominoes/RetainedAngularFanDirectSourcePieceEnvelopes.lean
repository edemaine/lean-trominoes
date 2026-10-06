/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedAngularFanDirectSourceRouteHull
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSpokeIdentification

/-! Linear envelopes for the small hulls of direct-source route pieces. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit

inductive DirectSourcePiece where
  | escape | tail | complete | spoke

namespace DirectSourcePiece

def route (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : DirectSourcePiece → List Cell
  | .escape => (retainedDirectSourceFanEscapeAt kind index slot).route
  | .tail => retainedDirectSourceFanCompleteTailAt kind index slot
  | .complete => retainedDirectSourceFanCompleteRouteAt kind index slot
  | .spoke => retainedDirectSourceFigure7SpokeAt kind index slot

def hull (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) : DirectSourcePiece → List Cell
  | .escape => (retainedDirectSourceFanEscapeAt kind index slot).route
  | .tail => retainedDirectSourceShiftedTailHull (retainedDirectSourceFanCenterAt kind index)
      (retainedDirectSourceFanTerminalAt kind index) slot ++
      retainedTerminalFanOuterLocalRouteAt (retainedDirectSourceFanCenterAt kind index)
        (retainedDirectSourceFanTerminalAt kind index).1 slot
  | .complete => retainedDirectSourceCompleteRouteHull kind index slot
  | .spoke => retainedDirectSourceFigure7SpokeAt kind index slot

theorem route_nonempty (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (piece : DirectSourcePiece) : route kind index slot piece ≠ [] := by
  have head : ∃ p, (route kind index slot piece).head? = some p := by
    cases piece with
    | escape => exact ⟨_, (retainedDirectSourceFanEscapeAt kind index slot).head_eq⟩
    | tail => exact ⟨_, retainedTerminalFanOuterCoordinatedEscapedCompleteTail_head? _ _ slot⟩
    | complete => exact ⟨_, retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_head?
        _ _ slot (retainedDirectSourceFanEscapeAt kind index slot)⟩
    | spoke => exact ⟨_, retainedDirectSourceFigure7SpokeAt_head? kind index slot⟩
  obtain ⟨p, hp⟩ := head
  intro empty
  simp [empty] at hp

theorem hull_linearBounds (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (piece : DirectSourcePiece) (normal : Cell) (lower upper : Int)
    (bounded : ∀ p ∈ hull kind index slot piece,
      lower ≤ Cell.linearValue normal p ∧ Cell.linearValue normal p ≤ upper)
    {p : Cell} (member : p ∈ route kind index slot piece) :
    lower ≤ Cell.linearValue normal p ∧ Cell.linearValue normal p ≤ upper := by
  cases piece with
  | escape => exact bounded p member
  | spoke => exact bounded p member
  | complete =>
      exact retainedDirectSourceCompleteRouteHull_linearBounds kind index slot
        normal lower upper bounded member
  | tail =>
    rcases mem_joinAtEndpoint member with shifted | localMember
    · exact retainedDirectSourceShiftedTailHull_linearBounds _ normal _ slot lower upper
        (fun q hq => bounded q (List.mem_append_left _ hq)) shifted
    · exact bounded p (List.mem_append_right _ localMember)

private theorem foldl_max_le (normal : Cell) (route : List Cell) (initial upper : Int)
    (initialBound : initial ≤ upper)
    (bounded : ∀ point ∈ route, Cell.linearValue normal point ≤ upper) :
    route.foldl (fun bound point => max bound (Cell.linearValue normal point)) initial ≤ upper := by
  induction route generalizing initial with
  | nil => exact initialBound
  | cons head tail ih =>
    exact ih _ (max_le initialBound (bounded _ (by simp)))
      (fun point member => bounded _ (by simp [member]))

private theorem foldl_min_ge (normal : Cell) (route : List Cell) (initial lower : Int)
    (initialBound : lower ≤ initial)
    (bounded : ∀ point ∈ route, lower ≤ Cell.linearValue normal point) :
    lower ≤ route.foldl (fun bound point => min bound (Cell.linearValue normal point)) initial := by
  induction route generalizing initial with
  | nil => exact initialBound
  | cons head tail ih =>
    exact ih _ (le_min initialBound (bounded _ (by simp)))
      (fun point member => bounded _ (by simp [member]))

private theorem maximum_le_of_bounded (normal : Cell) (route : List Cell) (upper : Int)
    (nonempty : route ≠ [])
    (bounded : ∀ point ∈ route, Cell.linearValue normal point ≤ upper) :
    routeLinearMaximum normal route ≤ upper := by
  cases route with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    exact foldl_max_le normal (head :: tail) _ upper
      (bounded _ (by simp)) bounded

private theorem minimum_ge_of_bounded (normal : Cell) (route : List Cell) (lower : Int)
    (nonempty : route ≠ [])
    (bounded : ∀ point ∈ route, lower ≤ Cell.linearValue normal point) :
    lower ≤ routeLinearMinimum normal route := by
  cases route with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    exact foldl_min_ge normal (head :: tail) _ lower
      (bounded _ (by simp)) bounded

theorem hull_envelope (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length)
    (slot : RetainedTerminalSlot) (piece : DirectSourcePiece) (normal : Cell) :
    routeLinearMaximum normal (route kind index slot piece) ≤ routeLinearMaximum normal (hull kind index slot piece) ∧
      routeLinearMinimum normal (hull kind index slot piece) ≤ routeLinearMinimum normal (route kind index slot piece) := by
  have bounded (p : Cell) (hp : p ∈ route kind index slot piece) :=
    hull_linearBounds kind index slot piece normal
      (routeLinearMinimum normal (hull kind index slot piece))
      (routeLinearMaximum normal (hull kind index slot piece))
      (fun q hq => ⟨routeLinearMinimum_le_linearValue normal _ hq,
        linearValue_le_routeLinearMaximum normal _ hq⟩) hp
  exact ⟨maximum_le_of_bounded _ _ _ (route_nonempty kind index slot piece)
      (fun p hp => (bounded p hp).2),
    minimum_ge_of_bounded _ _ _ (route_nonempty kind index slot piece)
      (fun p hp => (bounded p hp).1)⟩

end DirectSourcePiece

private theorem separatedBySome_of_mem (normals : List Cell) (first second : List Cell)
    {normal : Cell} (member : normal ∈ normals)
    (separated : RoutesLinearlySeparatedBy normal first second) :
    RoutesLinearlySeparatedBySome normals first second := by
  induction normals with
  | nil => simp at member
  | cons n ns ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl separated
    · exact Or.inr (ih member)

/-- Test the small envelopes against candidate separator normals. -/
def directSourcePieceSeparationCheck (normals : List Cell)
    (firstKind secondKind : RetainedDirectClauseKind)
    (firstIndex : Fin (retainedDirectSourcePrefixChoices firstKind).length)
    (secondIndex : Fin (retainedDirectSourcePrefixChoices secondKind).length)
    (firstSlot secondSlot : RetainedTerminalSlot) (firstPiece secondPiece : DirectSourcePiece) : Bool :=
  normals.any fun normal =>
    decide (routeLinearMaximum normal (firstPiece.hull firstKind firstIndex firstSlot) <
      routeLinearMinimum normal (secondPiece.hull secondKind secondIndex secondSlot) ∨
      routeLinearMaximum normal (secondPiece.hull secondKind secondIndex secondSlot) <
        routeLinearMinimum normal (firstPiece.hull firstKind firstIndex firstSlot))

/-- A small-envelope separator also separates the original route pieces. -/
theorem directSourcePieceSeparationCheck_sound (normals : List Cell)
    (firstKind secondKind : RetainedDirectClauseKind)
    (firstIndex : Fin (retainedDirectSourcePrefixChoices firstKind).length)
    (secondIndex : Fin (retainedDirectSourcePrefixChoices secondKind).length)
    (firstSlot secondSlot : RetainedTerminalSlot) (firstPiece secondPiece : DirectSourcePiece)
    (checked : directSourcePieceSeparationCheck normals firstKind secondKind firstIndex secondIndex
      firstSlot secondSlot firstPiece secondPiece = true) :
    RoutesLinearlySeparatedBySome normals (firstPiece.route firstKind firstIndex firstSlot)
      (secondPiece.route secondKind secondIndex secondSlot) := by
  simp only [directSourcePieceSeparationCheck, List.any_eq_true, decide_eq_true_eq] at checked
  obtain ⟨normal, member, separated⟩ := checked
  apply separatedBySome_of_mem normals _ _ member
  have first := firstPiece.hull_envelope firstKind firstIndex firstSlot normal
  have second := secondPiece.hull_envelope secondKind secondIndex secondSlot normal
  rcases separated with before | after
  · exact Or.inl (lt_of_le_of_lt first.1 (lt_of_lt_of_le before second.2))
  · exact Or.inr (lt_of_le_of_lt second.1 (lt_of_lt_of_le after first.2))

end LeanTrominoes.PeriodicEightOccurrenceSplit
