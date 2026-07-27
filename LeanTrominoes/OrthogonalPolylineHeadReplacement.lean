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

/-- Total name for the first point after a polyline's head.  Genuine routes
use the specification theorem below; the origin is only a harmless fallback
for malformed or singleton lists. -/
def polylineFirstExit (route : List Cell) : Cell :=
  route.tail.head?.getD (0, 0)

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

/-- Distinct advertised endpoints force a route to have a point after its
head. -/
theorem List.exists_tail_head?_of_endpoints_ne
    {α : Type*} {route : List α} {source target : α}
    (routeHead : route.head? = some source)
    (routeLast : route.getLast? = some target)
    (endpointsNe : source ≠ target) :
    ∃ exit, route.tail.head? = some exit := by
  cases route with
  | nil =>
      simp at routeHead
  | cons first rest =>
      cases rest with
      | nil =>
          have sourceEq :
              source = first :=
            (Option.some.inj routeHead).symm
          have targetEq :
              first = target :=
            Option.some.inj routeLast
          exact (endpointsNe (sourceEq.trans targetEq)).elim
      | cons second tail =>
          exact ⟨second, rfl⟩

/-- Mapping a route maps its first exit point. -/
theorem List.tail_head?_map
    {α β : Type*} (mapPoint : α → β)
    {route : List α} {exit : α}
    (tailHead : route.tail.head? = some exit) :
    (route.map mapPoint).tail.head? =
      some (mapPoint exit) := by
  simpa using congrArg (Option.map mapPoint) tailHead

/-- The total first-exit lookup returns the witnessed point on every
nondegenerate route. -/
theorem polylineFirstExit_eq
    {route : List Cell} {exit : Cell}
    (tailHead : route.tail.head? = some exit) :
    polylineFirstExit route = exit := by
  simp [polylineFirstExit, tailHead]

/-- A route with a witnessed first exit advertises the total lookup as that
same exit. -/
theorem polylineFirstExit_spec
    {route : List Cell}
    (tailNonempty : ∃ exit, route.tail.head? = some exit) :
    route.tail.head? =
      some (polylineFirstExit route) := by
  rcases tailNonempty with ⟨exit, tailHead⟩
  simpa [polylineFirstExit_eq tailHead] using tailHead

/-- Joining a suffix after a route with two or more points leaves the first
route's initial exit unchanged. -/
theorem joinAtEndpoint_tail_head?
    {α : Type*} {first second : List α} {exit : α}
    (firstTailHead : first.tail.head? = some exit) :
    (joinAtEndpoint first second).tail.head? =
      some exit := by
  cases first with
  | nil =>
      simp at firstTailHead
  | cons firstPoint rest =>
      cases rest with
      | nil =>
          simp at firstTailHead
      | cons secondPoint tail =>
          simpa [joinAtEndpoint] using firstTailHead

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
