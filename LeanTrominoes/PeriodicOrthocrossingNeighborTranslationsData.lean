/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.CellData

/-! # Fixed neighboring period translations -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The three neighboring cell coordinates. -/
def neighborCoordinates : List Int := [-1, 0, 1]

/-- The nine neighboring lattice-cell translations. -/
def neighborTranslations : List Cell :=
  neighborCoordinates.flatMap fun horizontal =>
    neighborCoordinates.map fun vertical =>
      (horizontal, vertical)

end LeanTrominoes.PeriodicOrthocrossing
