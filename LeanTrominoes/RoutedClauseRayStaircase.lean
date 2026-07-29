import LeanTrominoes.OctilinearEmbeddedCNFIncidenceDrawing
import LeanTrominoes.PlanarThreeSATDuplicatorArm
import LeanTrominoes.OrthogonalPolylineSymmetries

/-!
# Staircases for the three routed-clause rays

The direct routed source-clause star is the one retained component whose
segments are not restricted to the eight axis and 45-degree compass rays.
From the clause center `(10, 10)`, its three possible forward vectors are
`(-9, -4)`, `(-4, 1)`, and `(1, -4)`.

This file gives each primitive vector a balanced unit-step block and repeats
that block along positive integral multiples of the same ray.  Each block
returns exactly to the original straight ray, which will support the later
narrow-corridor planarity argument.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- Primitive forward vector from the routed clause center to one arm. -/
def routedClauseRayPrimitive : DuplicatorArm → Cell
  | .left => (-9, -4)
  | .middle => (-4, 1)
  | .right => (1, -4)

/-- Balanced unit-step offsets for one primitive routed-clause ray.
Every list starts at zero and ends at `routedClauseRayPrimitive arm`. -/
def routedClauseRayOffsets : DuplicatorArm → List Cell
  | .left =>
      [(0, 0), (-1, 0), (-2, 0), (-2, -1),
        (-3, -1), (-4, -1), (-4, -2), (-5, -2),
        (-6, -2), (-6, -3), (-7, -3), (-8, -3),
        (-8, -4), (-9, -4)]
  | .middle =>
      [(0, 0), (-1, 0), (-2, 0), (-2, 1),
        (-3, 1), (-4, 1)]
  | .right =>
      [(0, 0), (0, -1), (0, -2), (1, -2),
        (1, -3), (1, -4)]

@[simp]
theorem routedClauseRayOffsets_head?
    (arm : DuplicatorArm) :
    (routedClauseRayOffsets arm).head? = some (0, 0) := by
  cases arm <;> rfl

@[simp]
theorem routedClauseRayOffsets_getLast?
    (arm : DuplicatorArm) :
    (routedClauseRayOffsets arm).getLast? =
      some (routedClauseRayPrimitive arm) := by
  cases arm <;> rfl

/-- Each primitive block consists entirely of nondegenerate unit
horizontal and vertical steps. -/
theorem routedClauseRayOffsets_orthogonal
    (arm : DuplicatorArm) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (routedClauseRayOffsets arm) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
  cases arm <;> native_decide

/-- Place one primitive staircase block at an arbitrary start point. -/
def routedClauseRayBlock
    (arm : DuplicatorArm) (start : Cell) : List Cell :=
  (routedClauseRayOffsets arm).map (Cell.add start)

@[simp]
theorem routedClauseRayBlock_head?
    (arm : DuplicatorArm) (start : Cell) :
    (routedClauseRayBlock arm start).head? = some start := by
  simp [routedClauseRayBlock, Cell.add]

@[simp]
theorem routedClauseRayBlock_getLast?
    (arm : DuplicatorArm) (start : Cell) :
    (routedClauseRayBlock arm start).getLast? =
      some
        (Cell.add start
          (routedClauseRayPrimitive arm)) := by
  simp [routedClauseRayBlock]

/-- A translated primitive block remains orthogonal. -/
theorem routedClauseRayBlock_orthogonal
    (arm : DuplicatorArm) (start : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (routedClauseRayBlock arm start) := by
  simpa [routedClauseRayBlock,
    PeriodicOrthocrossing.translatePolyline] using
    (routedClauseRayOffsets_orthogonal arm).translate start

/-- Repeat the balanced primitive block along one routed-clause ray. -/
def routedClauseRay
    (arm : DuplicatorArm) : Nat → Cell → List Cell
  | 0, start => [start]
  | length + 1, start =>
      joinAtEndpoint
        (routedClauseRayBlock arm start)
        (routedClauseRay arm length
          (Cell.add start
            (routedClauseRayPrimitive arm)))

@[simp]
theorem routedClauseRay_head?
    (arm : DuplicatorArm) (length : Nat) (start : Cell) :
    (routedClauseRay arm length start).head? =
      some start := by
  cases length with
  | zero =>
      rfl
  | succ length =>
      rw [routedClauseRay]
      exact joinAtEndpoint_head?
        (routedClauseRayBlock_head? arm start)

@[simp]
theorem routedClauseRay_getLast?
    (arm : DuplicatorArm) (length : Nat) (start : Cell) :
    (routedClauseRay arm length start).getLast? =
      some
        (Cell.add start
          (Cell.scale length
            (routedClauseRayPrimitive arm))) := by
  induction length generalizing start with
  | zero =>
      simp [routedClauseRay, Cell.add, Cell.scale]
  | succ length induction =>
      rw [routedClauseRay]
      have joined :=
        joinAtEndpoint_getLast?
          (routedClauseRayBlock_getLast? arm start)
          (routedClauseRay_head? arm length
            (Cell.add start
              (routedClauseRayPrimitive arm)))
          (induction
            (Cell.add start
              (routedClauseRayPrimitive arm)))
      rw [joined]
      apply congrArg some
      apply Prod.ext <;>
        simp [Cell.add, Cell.scale] <;>
        ring

/-- Every repeated routed-clause staircase is orthogonal. -/
theorem routedClauseRay_orthogonal
    (arm : DuplicatorArm) (length : Nat) (start : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (routedClauseRay arm length start) := by
  induction length generalizing start with
  | zero =>
      simp [routedClauseRay,
        PeriodicOrthocrossing.OrthogonalPolyline]
  | succ length induction =>
      rw [routedClauseRay]
      apply
        (routedClauseRayBlock_orthogonal arm start).joinAtEndpoint
          (induction
            (Cell.add start
              (routedClauseRayPrimitive arm)))
      · exact routedClauseRayBlock_getLast? arm start
      · exact routedClauseRay_head? arm length
          (Cell.add start
            (routedClauseRayPrimitive arm))

/-! ## Executable ray classification -/

/-- Candidate repeat count for one of the three primitive rays. -/
def routedClauseRayLengthCandidate
    (arm : DuplicatorArm) (vector : Cell) : Nat :=
  match arm with
  | .left => vector.1.natAbs / 9
  | .middle => vector.1.natAbs / 4
  | .right => vector.1.natAbs

/-- Check whether a vector is a positive multiple of a given routed-clause
primitive ray. -/
def routedClauseRayMatches
    (arm : DuplicatorArm) (vector : Cell) : Bool :=
  let length := routedClauseRayLengthCandidate arm vector
  decide
    (0 < length ∧
      vector =
        Cell.scale length
          (routedClauseRayPrimitive arm))

/-- Classify the three extra retained ray slopes, in arm order. -/
def routedClauseRayClassify
    (vector : Cell) : Option (DuplicatorArm × Nat) :=
  if routedClauseRayMatches .left vector then
    some (.left,
      routedClauseRayLengthCandidate .left vector)
  else if routedClauseRayMatches .middle vector then
    some (.middle,
      routedClauseRayLengthCandidate .middle vector)
  else if routedClauseRayMatches .right vector then
    some (.right,
      routedClauseRayLengthCandidate .right vector)
  else
    none

/-- Successful classification exposes a positive repeat count and the exact
primitive-vector decomposition. -/
theorem routedClauseRayClassify_sound
    {vector : Cell} {arm : DuplicatorArm} {length : Nat}
    (classified :
      routedClauseRayClassify vector =
        some (arm, length)) :
    0 < length ∧
      vector =
        Cell.scale length
          (routedClauseRayPrimitive arm) := by
  unfold routedClauseRayClassify at classified
  split at classified
  next leftMatches =>
    have matchProperty :
        0 <
            routedClauseRayLengthCandidate
              .left vector ∧
          vector =
            Cell.scale
              (routedClauseRayLengthCandidate
                .left vector)
              (routedClauseRayPrimitive .left) := by
      simpa [routedClauseRayMatches] using
        leftMatches
    simp only [Option.some.injEq, Prod.mk.injEq]
      at classified
    rcases classified with ⟨rfl, rfl⟩
    exact matchProperty
  next leftMiss =>
    split at classified
    next middleMatches =>
      have matchProperty :
          0 <
              routedClauseRayLengthCandidate
                .middle vector ∧
            vector =
              Cell.scale
                (routedClauseRayLengthCandidate
                  .middle vector)
                (routedClauseRayPrimitive .middle) := by
        simpa [routedClauseRayMatches] using
          middleMatches
      simp only [Option.some.injEq, Prod.mk.injEq]
        at classified
      rcases classified with ⟨rfl, rfl⟩
      exact matchProperty
    next middleMiss =>
      split at classified
      next rightMatches =>
        have matchProperty :
            0 <
                routedClauseRayLengthCandidate
                  .right vector ∧
              vector =
                Cell.scale
                  (routedClauseRayLengthCandidate
                    .right vector)
                  (routedClauseRayPrimitive .right) := by
          simpa [routedClauseRayMatches] using
            rightMatches
        simp only [Option.some.injEq, Prod.mk.injEq]
          at classified
        rcases classified with ⟨rfl, rfl⟩
        exact matchProperty
      next rightMiss =>
        contradiction

/-- Every positive multiple of a primitive routed-clause ray is recognized
with its exact arm and repeat count. -/
@[simp]
theorem routedClauseRayClassify_scale
    (arm : DuplicatorArm) {length : Nat}
    (positive : 0 < length) :
    routedClauseRayClassify
        (Cell.scale length
          (routedClauseRayPrimitive arm)) =
      some (arm, length) := by
  cases arm <;>
    simp [routedClauseRayClassify,
      routedClauseRayMatches,
      routedClauseRayLengthCandidate,
      routedClauseRayPrimitive, Cell.scale,
      Int.natAbs_mul, Int.natAbs_neg,
      Int.natAbs_natCast, positive] <;>
    try omega
  case right =>
    split
    · next leftMatches =>
      rcases leftMatches with
        ⟨_, oppositeSigns, _⟩
      have nonnegative :
          (0 : Int) ≤
            (↑length / 9) * 9 := by
        positivity
      omega
    · split
      · next middleMatches =>
        rcases middleMatches with
          ⟨_, _, oppositeSigns⟩
        have nonnegative :
            (0 : Int) ≤ ↑length / 4 := by
          positivity
        omega
      · rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
