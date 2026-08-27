/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterization

/-! # Finite direction steps in strip-raster coordinates -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- Geometric vertical directions reverse under strip reflection; horizontal
directions retain their signs. -/
def stripDirectionStep : AxisDirection → Cell
  | .east => (1, 0)
  | .north => (0, -1)
  | .west => (-1, 0)
  | .south => (0, 1)
  | .invalid => (0, 0)

/-- Advance one already-rasterized point, reducing only its horizontal
coordinate modulo the strip period. -/
def advanceStripLocation (period : Nat) (location : Cell)
    (direction : AxisDirection) : Cell :=
  let step := stripDirectionStep direction
  ((location.1 + step.1) % period, location.2 + step.2)

/-- Rasterization commutes exactly with every finite direction step. -/
@[simp] theorem stripRasterLocation_add_directionStep
    (period : Nat) (point : Cell) (direction : AxisDirection) :
    stripRasterLocation period (Cell.add point direction.step) =
      advanceStripLocation period (stripRasterLocation period point)
        direction := by
  rcases point with ⟨horizontal, vertical⟩
  cases direction <;>
    simp [stripRasterLocation, advanceStripLocation, stripDirectionStep,
      AxisDirection.step, Cell.add, Int.add_emod] <;> omega

end PeriodicThreeDM
end LeanTrominoes
