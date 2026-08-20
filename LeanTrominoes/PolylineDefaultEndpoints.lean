/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Basic

/-! # Total polyline endpoint projections -/

namespace LeanTrominoes

/-- First polyline point, with the lattice origin as an empty fallback. -/
def polylineHeadD (points : List Cell) : Cell :=
  points.head?.getD (0, 0)

/-- Final polyline point, with the lattice origin as an empty fallback. -/
def polylineLastD (points : List Cell) : Cell :=
  points.getLastD (0, 0)

end LeanTrominoes
