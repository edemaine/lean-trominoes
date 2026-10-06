/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedRayRasterizationCorridor
import LeanTrominoes.OrthogonalPolylineLinearSeparation

/-!
# Constant-size linear bounds for repeated ray staircases

Every point of a repeated staircase is a primitive-block offset translated
by an intermediate multiple of the ray vector. A linear functional is
therefore bounded by the same offsets at the initial and final multiples.
This gives a constant-size hull regardless of the number of repeated blocks.
-/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT

/-- The listed offsets of one primitive staircase block. -/
def RetainedRay.blockOffsets : RetainedRay → List Cell
  | .compass port _ => compassRay port 1 (0, 0)
  | .routedClause arm _ => routedClauseRayOffsets arm

/-- A constant-size set bounding every linear functional on the raster. -/
def RetainedRay.linearHull (ray : RetainedRay) (start : Cell) : List Cell :=
  ray.blockOffsets.map (Cell.add start) ++
    ray.blockOffsets.map (Cell.add (Cell.add start ray.vector))

private theorem diagonalStaircase_mem_block
    (horizontal vertical : Int) (length : Nat) (start : Cell)
    {point : Cell} (member : point ∈ diagonalStaircase horizontal vertical length start) :
    ∃ index : Nat, index ≤ length ∧
      ∃ offset ∈ [(0, 0), (horizontal, 0), (horizontal, vertical)],
        point = Cell.add (Cell.add start (Cell.scale index (horizontal, vertical))) offset := by
  induction length generalizing start with
  | zero =>
    simp only [diagonalStaircase, List.mem_singleton] at member
    subst point
    exact ⟨0, le_refl _, (0, 0), by simp, by simp [Cell.add, Cell.scale]⟩
  | succ length ih =>
    simp only [diagonalStaircase, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact ⟨0, Nat.zero_le _, (0, 0), by simp, by simp [Cell.add, Cell.scale]⟩
    · exact ⟨0, Nat.zero_le _, (horizontal, 0), by simp, by simp [Cell.add, Cell.scale]⟩
    · rcases ih _ member with ⟨index, bound, offset, offsetMember, equal⟩
      refine ⟨index + 1, by omega, offset, offsetMember, ?_⟩
      rw [equal]
      apply Prod.ext <;> simp [Cell.add, Cell.scale, Nat.cast_add] <;> ring

private theorem routedClauseRay_mem_block
    (arm : DuplicatorArm) (length : Nat) (start : Cell)
    {point : Cell} (member : point ∈ routedClauseRay arm length start) :
    ∃ index : Nat, index ≤ length ∧
      ∃ offset ∈ routedClauseRayOffsets arm,
        point = Cell.add (Cell.add start (Cell.scale index (routedClauseRayPrimitive arm))) offset := by
  induction length generalizing start with
  | zero =>
    simp only [routedClauseRay, List.mem_singleton] at member
    subst point
    refine ⟨0, le_refl _, (0, 0), ?_, by simp [Cell.add, Cell.scale]⟩
    cases arm <;> simp [routedClauseRayOffsets]
  | succ length ih =>
    rw [routedClauseRay] at member
    rcases mem_joinAtEndpoint member with member | member
    · rcases List.mem_map.mp member with ⟨offset, offsetMember, rfl⟩
      exact ⟨0, Nat.zero_le _, offset, offsetMember, by simp [Cell.add, Cell.scale]⟩
    · rcases ih _ member with ⟨index, bound, offset, offsetMember, equal⟩
      refine ⟨index + 1, by omega, offset, offsetMember, ?_⟩
      rw [equal]
      apply Prod.ext <;> simp [Cell.add, Cell.scale, Nat.cast_add] <;> ring

private theorem RetainedRay.rasterize_mem_block
    (ray : RetainedRay) (start : Cell) {point : Cell}
    (member : point ∈ ray.rasterize start) :
    ∃ index : Nat, index ≤ ray.length ∧
      ∃ offset ∈ ray.blockOffsets,
        point = Cell.add (Cell.add start (Cell.scale index ray.primitive)) offset := by
  cases ray with
  | routedClause arm length => exact routedClauseRay_mem_block arm length start member
  | compass port length =>
    cases length with
    | zero =>
      simp only [RetainedRay.rasterize, compassRay, List.mem_singleton] at member
      subst point
      refine ⟨0, le_refl _, (0, 0), ?_, by simp [Cell.add, Cell.scale]⟩
      cases port <;> simp [RetainedRay.blockOffsets, compassRay, diagonalStaircase]
    | succ length =>
      cases port <;>
        simp only [RetainedRay.rasterize, compassRay] at member
      all_goals first
        | simpa [RetainedRay.length, RetainedRay.blockOffsets, RetainedRay.primitive,
            compassRay, diagonalStaircase, Port.unitVector, Cell.add, Cell.scale] using
            diagonalStaircase_mem_block _ _ (length + 1) start member
        | simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · refine ⟨0, Nat.zero_le _, (0, 0), ?_, by simp [Cell.add, Cell.scale]⟩
            simp [RetainedRay.blockOffsets, compassRay, Port.unitVector, Cell.add, Cell.scale]
          · refine ⟨length + 1, le_refl _, (0, 0), ?_, ?_⟩
            · simp [RetainedRay.blockOffsets, compassRay, Port.unitVector, Cell.add, Cell.scale]
            · simp [RetainedRay.primitive, Cell.add, Cell.scale]

/-- Bounds on the constant-size hull bound every point of the full raster. -/
theorem RetainedRay.rasterize_linearBounds_of_hull
    (ray : RetainedRay) (start normal : Cell) (lower upper : Int)
    (bounded : ∀ point ∈ ray.linearHull start,
      lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper)
    {point : Cell} (member : point ∈ ray.rasterize start) :
    lower ≤ Cell.linearValue normal point ∧ Cell.linearValue normal point ≤ upper := by
  rcases ray.rasterize_mem_block start member with ⟨index, indexBound, offset, offsetMember, equal⟩
  have firstMember : Cell.add start offset ∈ ray.linearHull start :=
    List.mem_append_left _ (List.mem_map.mpr ⟨offset, offsetMember, rfl⟩)
  have lastMember : Cell.add (Cell.add start ray.vector) offset ∈ ray.linearHull start :=
    List.mem_append_right _ (List.mem_map.mpr ⟨offset, offsetMember, rfl⟩)
  have firstBound := bounded _ firstMember
  have lastBound := bounded _ lastMember
  have vectorEq : ray.vector = Cell.scale ray.length ray.primitive := by cases ray <;> rfl
  let initial := Cell.linearValue normal (Cell.add start offset)
  let step := Cell.linearValue normal ray.primitive
  have pointValue : Cell.linearValue normal point = initial + (index : Int) * step := by
    rw [equal]
    simp [initial, step, Cell.linearValue, Cell.add, Cell.scale]
    ring
  have lastValue : Cell.linearValue normal (Cell.add (Cell.add start ray.vector) offset) =
      initial + (ray.length : Int) * step := by
    rw [vectorEq]
    simp [initial, step, Cell.linearValue, Cell.add, Cell.scale]
    ring
  rw [lastValue] at lastBound
  have indexNonneg : (0 : Int) ≤ index := by omega
  have bound : (index : Int) ≤ ray.length := by exact_mod_cast indexBound
  rw [pointValue]
  change lower ≤ initial ∧ initial ≤ upper at firstBound
  by_cases nonnegative : 0 ≤ step
  · constructor <;> nlinarith [mul_nonneg indexNonneg nonnegative,
      mul_nonneg (sub_nonneg.mpr bound) nonnegative]
  · have negative : step ≤ 0 := by omega
    constructor <;> nlinarith [mul_nonpos_of_nonneg_of_nonpos indexNonneg negative,
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr bound) negative]

end LeanTrominoes.PeriodicEightOccurrenceSplit
