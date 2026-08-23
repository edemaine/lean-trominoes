/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATDuplicatorArmData
import LeanTrominoes.OrthogonalPolylineRibbon

/-! # Static first directions of routed-variable routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PlanarThreeSAT

/-- The finite table of first compass directions in the three fixed
duplicator-arm drawings.  Out-of-range indices retain the drawing's invalid
fallback. -/
def routedVariableRouteFirstDirection
    (arm : DuplicatorArm)
    (localClauseIndex literalIndex : Nat) : AxisDirection :=
  match arm, localClauseIndex, literalIndex with
  | .left, 0, 0 => .invalid
  | .left, 0, 1 => .east
  | .left, 1, 0 => .west
  | .left, 1, 1 => .invalid
  | .middle, 0, 0 => .invalid
  | .middle, 0, 1 => .invalid
  | .middle, 1, 0 => .north
  | .middle, 1, 1 => .south
  | .right, 0, 0 => .east
  | .right, 0, 1 => .north
  | .right, 1, 0 => .invalid
  | .right, 1, 1 => .invalid
  | _, _, _ => .invalid

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
