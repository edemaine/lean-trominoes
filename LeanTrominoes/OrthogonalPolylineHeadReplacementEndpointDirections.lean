import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.OrthogonalPolylineHeadReplacement

namespace LeanTrominoes
namespace AxisDirection

/-- Replacing the initial point and prefix of a route with at least three
points preserves its final direction. -/
theorem polylineLastDirection_replacePolylineHead
    {replacement route : List Cell} {middle : Cell}
    (replacementLast : replacement.getLast? = some middle)
    (tailHead : route.tail.head? = some middle)
    (routeLength : 3 ≤ route.length) :
    polylineLastDirection
        (replacePolylineHead replacement route) =
      polylineLastDirection route := by
  cases route with
  | nil =>
      simp at routeLength
  | cons first rest =>
      cases rest with
      | nil =>
          simp at routeLength
      | cons second rest =>
          cases rest with
          | nil =>
              simp at routeLength
          | cons third rest =>
              rw [show
                replacePolylineHead replacement
                    (first :: second :: third :: rest) =
                  joinAtEndpoint replacement
                    (second :: third :: rest) by
                    rfl]
              rw [polylineLastDirection_joinAtEndpoint
                replacementLast
                (by simpa using tailHead)
                (by simp)]
              exact
                (polylineLastDirection_cons_cons_cons
                  first second third rest).symm

end AxisDirection
end LeanTrominoes
