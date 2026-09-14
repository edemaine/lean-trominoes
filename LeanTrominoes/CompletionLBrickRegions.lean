/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBricks

namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxRecDepth 16384
set_option maxHeartbeats 0

noncomputable def minorRegion (v : Cell) : Finset Cell :=
  LEqBoundary.pattern.region.image (Cell.add v)

theorem minor_shapes :
    LNegBoundary.pattern.region = LEqBoundary.pattern.region ∧
    LPlugTopBoundary.pattern.region = LEqBoundary.pattern.region ∧
    LPlugBotBoundary.pattern.region = LEqBoundary.pattern.region := by decide +kernel

@[simp] theorem upper_region (i : Fin 24) (port : Fin 4) (v : Cell) :
    atomRegion (upperOuter i port,v) = minorRegion v := by
  unfold atomRegion upperOuter
  split <;> simp [Atom.pattern,minorRegion,minor_shapes.1,minor_shapes.2.1]

@[simp] theorem lower_region (i : Fin 24) (port : Fin 4) (v : Cell) :
    atomRegion (lowerOuter i port,v) = minorRegion v := by
  unfold atomRegion lowerOuter
  split <;> simp [Atom.pattern,minorRegion,minor_shapes.1,minor_shapes.2.2]

@[simp] theorem inner_region (i : Fin 24) (port : Fin 4) (v : Cell) :
    atomRegion (inner i port,v) = minorRegion v := by
  unfold atomRegion inner
  split <;> simp [Atom.pattern,minorRegion,minor_shapes.1]

@[simp] theorem equal_region (v : Cell) : atomRegion (.equal,v) = minorRegion v := rfl

theorem copy_region : atomRegion (.copy,(0,12)) =
    minorRegion (0,12) ∪ (minorRegion (12,12) ∪
      (minorRegion (0,18) ∪ minorRegion (12,18))) := by decide +kernel

theorem clause_region : atomRegion (.clause,(0,18)) =
    minorRegion (0,18) ∪ minorRegion (12,18) := by decide +kernel

noncomputable def uniformRegion : Finset Cell :=
  minorRegion (0,0) ∪ (minorRegion (12,0) ∪
  (minorRegion (0,6) ∪ (minorRegion (12,6) ∪
  (minorRegion (0,12) ∪ (minorRegion (12,12) ∪
  (minorRegion (0,18) ∪ (minorRegion (12,18) ∪
  (minorRegion (0,24) ∪ (minorRegion (12,24) ∪
  (minorRegion (0,30) ∪ minorRegion (12,30)))))))))))

/-- Every palette entry occupies exactly the same closed brick shape. -/
theorem region_uniform (i : Fin 24) : region i = uniformRegion := by
  by_cases h : i.val < 16 <;>
    simp [region,layout,h,uniformRegion,copy_region,clause_region,Finset.union_assoc]

end LeanTrominoes.CompletionPattern.LBricks
