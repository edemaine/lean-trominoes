import LeanTrominoes.RetainedAngularFanSourceEscapedSpliceSeparation

/-!
# Singleton escaped source splices

When deleting the old variable endpoint leaves a singleton source prefix,
that unique point is the escaped fan's source gate.  Replacing the old tail
therefore returns the escaped complete fan itself.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Joining a singleton to a nonempty route at that route's head changes
nothing. -/
private theorem joinAtEndpoint_singleton_left_of_head
    {α : Type*} (point : α) (route : List α)
    (head : route.head? = some point) :
    joinAtEndpoint [point] route = route := by
  cases route with
  | nil =>
      simp at head
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst first
      rfl

@[simp]
private theorem cell_scale_one (point : Cell) :
    Cell.scale (↑(1 : Nat) : Int) point = point := by
  rcases point with ⟨x, y⟩
  simp [Cell.scale]

@[simp]
private theorem scalePolyline_one (route : List Cell) :
    scalePolyline (↑(1 : Nat) : Int) route = route := by
  induction route with
  | nil => rfl
  | cons point points induction =>
      simpa only [scalePolyline_cons, cell_scale_one] using
        congrArg (List.cons point) induction

/-- An escaped splice with a singleton retained source prefix is exactly
its escaped complete outer-fan route. -/
theorem
    retainedAngularFanEscapedSplicedBoundaryPolyline_eq_outerCompleteRoute_of_singletonPrefix
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (singletonPrefix : route.dropLast.length = 1) :
    retainedAngularFanEscapedSplicedBoundaryPolyline
        route terminal slot =
      retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.scale retainedTerminalFanTotalRefinement
          (route.getLastD (0, 0)))
        terminal slot := by
  let center :=
    Cell.scale retainedTerminalFanTotalRefinement
      (route.getLastD (0, 0))
  let replacement :=
    retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot
  let gate :=
    (retainedAngularFanOuterDemand
      center terminal slot).gate
  have terminalScaleOne :
      scaleRetainedTerminalData 1 terminal = terminal := by
    rcases terminal with ⟨direction, length⟩
    simp [scaleRetainedTerminalData]
  have prefixEq :
      (scalePolyline retainedTerminalFanTotalRefinement
        route).dropLast = [gate] := by
    have scaledPrefix :=
      retainedAngularFanSourceScaledPrefix_eq_singleton_gate
        (factor := 1) (by decide)
        route terminal slot routeLength classified singletonPrefix
    rw [scalePolyline_one, terminalScaleOne] at scaledPrefix
    simpa [center, gate] using scaledPrefix
  have replacementHead :
      replacement.head? = some gate := by
    exact retainedTerminalFanOuterEscapedCompleteRoute_head?
      center terminal slot
  have prefixLast :
      (scalePolyline retainedTerminalFanTotalRefinement
        route).dropLast.getLast? = some gate := by
    rw [prefixEq]
    rfl
  rw [retainedAngularFanEscapedSplicedBoundaryPolyline,
    replacePolylineTail_eq_joinAtEndpoint_dropLast
      (scalePolyline retainedTerminalFanTotalRefinement route)
      replacement prefixLast replacementHead,
    prefixEq]
  exact
    joinAtEndpoint_singleton_left_of_head
      gate replacement replacementHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes
