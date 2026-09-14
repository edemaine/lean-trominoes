/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubeHardness
import LeanTrominoes.ThreeTranslationPolycubeUpperBound
import LeanTrominoes.ThreeTranslationPolycubeFixed

/-! # Corollary 5.9: three connected polycubes, translations only -/

namespace LeanTrominoes.ThreeTranslationPolycubes

/-- Full-space tiling by translations of two fixed connected polycubes and an
input connected polycube is co-r.e.-complete. Each fixed tile has 45 voxels. -/
theorem spaceProved : spaceStatement := ⟨space_coRE,space_coREHard⟩

/-- For every fixed height greater than one, slab tiling by translations of
three connected polycubes is co-r.e.-complete, with at most 45 voxels in each
of the two fixed tiles. -/
theorem slabsProved : slabsStatement := fun height hh =>
  ⟨slab_coRE height,slabs_coREHard height hh⟩

/-- Both assertions of Corollary 5.9. -/
theorem proved : statement := ⟨spaceProved,slabsProved⟩

end LeanTrominoes.ThreeTranslationPolycubes
