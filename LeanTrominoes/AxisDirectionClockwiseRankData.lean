/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineRibbon

/-! # Clockwise ranks of axis directions -/

namespace LeanTrominoes
namespace AxisDirection

/-- Clockwise rank beginning at east.  The invalid fallback lies outside the
four genuine ranks. -/
def clockwiseRank : AxisDirection → Nat
  | .east => 0
  | .south => 1
  | .west => 2
  | .north => 3
  | .invalid => 4

end AxisDirection
end LeanTrominoes
