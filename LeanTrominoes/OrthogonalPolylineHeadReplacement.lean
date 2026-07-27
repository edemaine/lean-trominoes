import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Replacing the head of an orthogonal polyline

Local vertex gadgets replace a source vertex by several distinct boundary
ports.  To attach those ports without routing every new incidence back through
the old source point, we discard the old route's first listed point and join a
new prefix directly to the first point of its tail.

`replacePolylineHead` packages that operation.  This file proves that the new
prefix determines the source endpoint, the untouched tail preserves the old
target endpoint, and orthogonality composes across the splice.
-/

namespace LeanTrominoes

/-- Replace the first listed point of `route` by `replacement`, joining it to
the first point of `route.tail`.  The endpoint agreement needed at that join
is expressed by the theorems below rather than built into this definition. -/
def replacePolylineHead {α : Type*}
    (replacement route : List α) : List α :=
  joinAtEndpoint replacement route.tail

/-- A nonempty replacement prefix determines the new source endpoint. -/
theorem replacePolylineHead_head?
    {replacement route : List Cell} {source : Cell}
    (replacementHead : replacement.head? = some source) :
    (replacePolylineHead replacement route).head? = some source :=
  joinAtEndpoint_head? replacementHead

/-- Removing the head of a route with a nonempty tail preserves its final
endpoint. -/
theorem List.getLast?_tail_eq_getLast?
    {α : Type*} {route : List α} {middle target : α}
    (tailHead : route.tail.head? = some middle)
    (routeLast : route.getLast? = some target) :
    route.tail.getLast? = some target := by
  cases route with
  | nil =>
      simp at tailHead
  | cons first rest =>
      cases rest with
      | nil =>
          simp at tailHead
      | cons second tail =>
          simpa using routeLast

/-- A replacement prefix joined to the old route's nonempty tail preserves
the old target endpoint. -/
theorem replacePolylineHead_getLast?
    {replacement route : List Cell}
    {middle target : Cell}
    (replacementLast : replacement.getLast? = some middle)
    (tailHead : route.tail.head? = some middle)
    (routeLast : route.getLast? = some target) :
    (replacePolylineHead replacement route).getLast? =
      some target := by
  apply joinAtEndpoint_getLast? replacementLast tailHead
  exact List.getLast?_tail_eq_getLast? tailHead routeLast

/-- Orthogonality survives replacement of a route's first point when the new
prefix is orthogonal and meets the old tail at its first point. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.replaceHead
    {replacement route : List Cell} {middle : Cell}
    (replacementOrthogonal : OrthogonalPolyline replacement)
    (routeOrthogonal : OrthogonalPolyline route)
    (replacementLast : replacement.getLast? = some middle)
    (tailHead : route.tail.head? = some middle) :
    OrthogonalPolyline
      (LeanTrominoes.replacePolylineHead replacement route) := by
  exact replacementOrthogonal.joinAtEndpoint
    routeOrthogonal.tail replacementLast tailHead

end LeanTrominoes
