/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PlusRefinement
import LeanTrominoes.PolyominoConnectivity
import LeanTrominoes.TilingPair
import LeanWang.CoRE

/-!
# Theorem 5.5: plane target

P is the fixed connected 15-omino. The input is an explicit list of cells
for Q; repeated cells are ignored. Empty or connected Q inputs are rejected.
This module defines the target proposition. `Theorem55Proof` supplies its proof.
-/

namespace LeanTrominoes.Theorem55

/-- Plane tiling by the fixed P and an input-dependent disconnected Q. -/
def planeProblem (input : List Cell) : Prop :=
  input.toFinset.Nonempty ∧ ¬ Polyomino.IsConnected input.toFinset ∧
    Tileable (pairTiles PlusRefinement.bumpy input.toFinset) Set.univ

/-- The plane assertion, with a single fixed choice of the connected tile. -/
def planeStatement : Prop := LeanWang.CoREComplete planeProblem

end LeanTrominoes.Theorem55
