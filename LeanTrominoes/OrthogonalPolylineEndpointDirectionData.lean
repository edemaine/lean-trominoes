/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineRibbon

/-! # Endpoint directions of polylines -/

namespace LeanTrominoes
namespace AxisDirection

/-- Direction of the first listed edge of a polyline, with the invalid
fallback on lists containing fewer than two points. -/
def polylineFirstDirection : List Cell → AxisDirection
  | first :: second :: _ => between first second
  | _ => .invalid

/-- Direction of the final listed edge of a polyline, with the invalid
fallback on lists containing fewer than two points. -/
def polylineLastDirection (points : List Cell) : AxisDirection :=
  (polylineFirstDirection points.reverse).opposite

end AxisDirection
end LeanTrominoes
