/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalPointBlockData

/-! # Duplicate freedom of the fundamental point scan -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The half-open list of integer coordinates contains no duplicates. -/
theorem fundamentalCoordinates_nodup
    {Vertex : Type*} (graph : PeriodicGraph Vertex) :
    (fundamentalCoordinates graph).Nodup := by
  unfold fundamentalCoordinates
  exact List.nodup_range.map fun _first _second equal =>
    Int.ofNat_inj.mp equal

/-- The row-major fundamental-square point scan contains no duplicates. -/
theorem fundamentalPoints_nodup
    {Vertex : Type*} (graph : PeriodicGraph Vertex) :
    (fundamentalPoints graph).Nodup := by
  change
    (fundamentalCoordinates graph ×ˢ
      fundamentalCoordinates graph).Nodup
  exact (fundamentalCoordinates_nodup graph).product
    (fundamentalCoordinates_nodup graph)

end LeanTrominoes.PeriodicOrthocrossing
