import LeanTrominoes.PeriodicOrthocrossingOrthogonal
import Mathlib.Data.List.Chain

/-!
# Joining orthogonal routes at a common endpoint

Route layers in the reduction are assembled from independently certified
prefixes and local gadget suffixes.  `joinAtEndpoint` removes the duplicated
common endpoint by retaining the first route and appending the tail of the
second.

This file proves the three facts needed by every such splice: the outer
endpoints are preserved, and orthogonality is preserved when both pieces are
orthogonal and their advertised endpoints agree.
-/

namespace LeanTrominoes

/-- Concatenate two routes while listing their common endpoint only once. -/
def joinAtEndpoint (first second : List Cell) : List Cell :=
  first ++ second.tail

/-- A nonempty first route determines the joined route's first endpoint. -/
theorem joinAtEndpoint_head?
    {first second : List Cell} {source : Cell}
    (firstHead : first.head? = some source) :
    (joinAtEndpoint first second).head? = some source := by
  cases first with
  | nil =>
      simp at firstHead
  | cons point rest =>
      simpa [joinAtEndpoint] using firstHead

/-- Matching middle endpoints and a nonempty suffix determine the joined
route's final endpoint. -/
theorem joinAtEndpoint_getLast?
    {first second : List Cell}
    {middle target : Cell}
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle)
    (secondLast : second.getLast? = some target) :
    (joinAtEndpoint first second).getLast? =
      some target := by
  cases second with
  | nil =>
      simp at secondHead
  | cons secondFirst secondRest =>
      cases secondRest with
      | nil =>
          have middleEqual :
              middle = secondFirst :=
            Option.some.inj secondHead.symm
          have targetEqual :
              target = secondFirst :=
            Option.some.inj secondLast.symm
          simpa [joinAtEndpoint, middleEqual,
            targetEqual] using firstLast
      | cons secondNext secondTail =>
          simpa [joinAtEndpoint] using secondLast

/-- Orthogonality is preserved when two orthogonal routes are joined at
their common endpoint. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.joinAtEndpoint
    {first second : List Cell} {middle : Cell}
    (firstOrthogonal : OrthogonalPolyline first)
    (secondOrthogonal : OrthogonalPolyline second)
    (firstLast : first.getLast? = some middle)
    (secondHead : second.head? = some middle) :
    OrthogonalPolyline (LeanTrominoes.joinAtEndpoint first second) := by
  unfold OrthogonalPolyline at firstOrthogonal secondOrthogonal ⊢
  cases first with
  | nil =>
      simp at firstLast
  | cons firstPoint firstRest =>
      cases second with
      | nil =>
          simp at secondHead
      | cons secondPoint secondRest =>
          cases secondRest with
          | nil =>
              simpa [LeanTrominoes.joinAtEndpoint] using
                firstOrthogonal
          | cons secondNext secondTail =>
              have secondParts :=
                List.isChain_cons_cons.mp secondOrthogonal
              apply List.IsChain.append
                firstOrthogonal secondParts.2
              intro lastPoint lastMember
                nextPoint nextMember
              have lastEqual :
                  lastPoint = middle := by
                rw [firstLast] at lastMember
                simpa using lastMember.symm
              have secondEqual :
                  secondPoint = middle :=
                Option.some.inj secondHead
              have nextEqual :
                  nextPoint = secondNext := by
                simpa using nextMember.symm
              subst lastPoint
              subst secondPoint
              subst nextPoint
              exact secondParts.1

end LeanTrominoes
