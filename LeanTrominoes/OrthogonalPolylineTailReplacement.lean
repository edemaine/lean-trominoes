import LeanTrominoes.OrthogonalPolylineHeadReplacement
import LeanTrominoes.OrthogonalPolylineSymmetries

/-!
# Replacing the tail of an orthogonal polyline

Occurrence-splitting gadgets preserve the clause-side prefix of an incidence
route and replace its old variable-side terminal neighborhood by a new local
fan.  `replacePolylineTail` is the exact reverse dual of
`replacePolylineHead`: it removes the old route's final point, joins a
replacement suffix at the preceding point, and preserves the old source
endpoint.
-/

namespace LeanTrominoes

/-- Replace the last listed point of `route` by `replacement`, joining the
first point of the replacement to the point immediately before the old
route's last point. -/
def replacePolylineTail {α : Type*}
    (route replacement : List α) : List α :=
  (replacePolylineHead replacement.reverse route.reverse).reverse

/-- Total name for the point immediately before a polyline's last point. -/
def polylineLastEntrance (route : List Cell) : Cell :=
  polylineFirstExit route.reverse

/-- A witnessed penultimate point is returned by the total last-entrance
lookup. -/
theorem polylineLastEntrance_eq
    {route : List Cell} {entrance : Cell}
    (reverseTailHead :
      route.reverse.tail.head? = some entrance) :
    polylineLastEntrance route = entrance :=
  polylineFirstExit_eq reverseTailHead

/-- A route with a witnessed penultimate point advertises the total lookup
as that same point. -/
theorem polylineLastEntrance_spec
    {route : List Cell}
    (reverseTailNonempty :
      ∃ entrance, route.reverse.tail.head? = some entrance) :
    route.reverse.tail.head? =
      some (polylineLastEntrance route) :=
  polylineFirstExit_spec reverseTailNonempty

/-- A nonempty replacement suffix determines the new target endpoint. -/
theorem replacePolylineTail_getLast?
    {route replacement : List Cell} {target : Cell}
    (replacementLast : replacement.getLast? = some target) :
    (replacePolylineTail route replacement).getLast? =
      some target := by
  rw [replacePolylineTail, List.getLast?_reverse]
  apply replacePolylineHead_head?
  simpa using replacementLast

/-- A replacement joined at the old penultimate point preserves the old
source endpoint. -/
theorem replacePolylineTail_head?
    {route replacement : List Cell}
    {source middle : Cell}
    (replacementHead : replacement.head? = some middle)
    (reverseTailHead :
      route.reverse.tail.head? = some middle)
    (routeHead : route.head? = some source) :
    (replacePolylineTail route replacement).head? =
      some source := by
  rw [replacePolylineTail, List.head?_reverse]
  apply replacePolylineHead_getLast?
  · simpa using replacementHead
  · exact reverseTailHead
  · simpa using routeHead

/-- Orthogonality survives replacement of a route's final point when the
new suffix is orthogonal and begins at the old penultimate point. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.replaceTail
    {route replacement : List Cell} {middle : Cell}
    (routeOrthogonal : OrthogonalPolyline route)
    (replacementOrthogonal : OrthogonalPolyline replacement)
    (replacementHead : replacement.head? = some middle)
    (reverseTailHead :
      route.reverse.tail.head? = some middle) :
    OrthogonalPolyline
      (LeanTrominoes.replacePolylineTail route replacement) := by
  unfold LeanTrominoes.replacePolylineTail
  apply
    (replacementOrthogonal.reverse.replaceHead
      routeOrthogonal.reverse
      (by simpa using replacementHead)
      reverseTailHead).reverse

end LeanTrominoes
