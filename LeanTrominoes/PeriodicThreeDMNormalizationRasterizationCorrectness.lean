/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRasterization

/-!
# Correctness of normalized-route rasterization

This module proves the local facts used to verify the normalized periodic
orthogonal drawing.  In particular, a routing cell exposes exactly the two
ports selected by its predecessor and successor, and the row-major array
compiler returns the assignment lookup at each stored torus position.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- A routing cell exposes its selected pair of distinct sides, both with
the route color, and has no other ports. -/
theorem routingCellType_portColor
    (first second side : Side) (color : WireColor) :
    (routingCellType first second color).portColor side =
      if first ≠ second ∧ (side = first ∨ side = second) then
        some color
      else
        none := by
  cases first <;> cases second <;> cases side <;>
    simp [routingCellType, OrthogonalCellType.portColor]

/-- Reversing a genuine geometric direction gives the opposite drawing-cell
side. -/
theorem Side.ofAxisDirection_opposite
    {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    Side.ofAxisDirection direction.opposite =
      (Side.ofAxisDirection direction).opposite := by
  cases direction <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.opposite,
      Side.ofAxisDirection, Side.opposite]

/-- Genuine geometric directions remain distinct after conversion to cell
sides. -/
theorem Side.ofAxisDirection_injective_of_genuine
    {first second : AxisDirection}
    (firstGenuine : first.IsGenuine)
    (secondGenuine : second.IsGenuine)
    (different : first ≠ second) :
    Side.ofAxisDirection first ≠ Side.ofAxisDirection second := by
  cases first <;> cases second <;>
    simp_all [AxisDirection.IsGenuine, Side.ofAxisDirection]

/-- A well-behaved internal route point has exactly the two colored ports
leading to its predecessor and successor. -/
theorem routingCellTypeAt_portColor
    {before current after : Cell}
    (incomingUnit : AxisDirection.IsUnitAxisStep before current)
    (outgoingUnit : AxisDirection.IsUnitAxisStep current after)
    (noReverse :
      AxisDirection.between current after ≠
        (AxisDirection.between before current).opposite)
    (color : WireColor) (side : Side) :
    (routingCellTypeAt before current after color).portColor side =
      if side = Side.ofAxisDirection
          (AxisDirection.between current before) ∨
        side = Side.ofAxisDirection
          (AxisDirection.between current after) then
        some color
      else
        none := by
  have incomingGenuine :
      (AxisDirection.between before current).IsGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep incomingUnit
  have outgoingGenuine :
      (AxisDirection.between current after).IsGenuine :=
    AxisDirection.between_isGenuine_of_unitAxisStep outgoingUnit
  have backwards :
      AxisDirection.between current before =
        (AxisDirection.between before current).opposite :=
    AxisDirection.between_reverse_eq_opposite incomingGenuine
  have distinctDirections :
      AxisDirection.between current before ≠
        AxisDirection.between current after := by
    rw [backwards]
    exact Ne.symm noReverse
  have backwardsGenuine :
      (AxisDirection.between current before).IsGenuine := by
    rw [backwards]
    exact AxisDirection.opposite_isGenuine incomingGenuine
  have distinctSides :
      Side.ofAxisDirection (AxisDirection.between current before) ≠
        Side.ofAxisDirection (AxisDirection.between current after) :=
    Side.ofAxisDirection_injective_of_genuine
      backwardsGenuine outgoingGenuine distinctDirections
  simp [routingCellTypeAt, routingCellType_portColor, distinctSides]

/-- Indexing a concatenation of equal-width rows selects the expected row.
This small list lemma is the bookkeeping core of the row-major compiler. -/
theorem List.getD_flatMap_fixedLength
    {α β : Type*} (rows : List α) (row : α → List β)
    (width rowIndex columnIndex : Nat) (fallback : β)
    (rowLength : ∀ item ∈ rows, (row item).length = width)
    (rowIndexValid : rowIndex < rows.length)
    (columnIndexValid : columnIndex < width) :
    (rows.flatMap row).getD
        (rowIndex * width + columnIndex) fallback =
      (row rows[rowIndex]).getD columnIndex fallback := by
  induction rows generalizing rowIndex with
  | nil => simp at rowIndexValid
  | cons first rest induction =>
      have firstLength : (row first).length = width :=
        rowLength first (by simp)
      have restLengths :
          ∀ item ∈ rest, (row item).length = width := by
        intro item member
        exact rowLength item (by simp [member])
      cases rowIndex with
      | zero =>
          rw [List.flatMap_cons, List.getD_append _ _ _ _]
          · simp
          · simpa [firstLength] using columnIndexValid
      | succ rowIndex =>
          have widthPositive : 0 < width :=
            Nat.zero_lt_of_lt columnIndexValid
          have appendRight :
              (row first).length ≤
                Nat.succ rowIndex * width + columnIndex := by
            rw [firstLength, Nat.succ_mul]
            omega
          rw [List.flatMap_cons,
            List.getD_append_right _ _ _ _ appendRight]
          have indexEquation :
              Nat.succ rowIndex * width + columnIndex -
                  (row first).length =
                rowIndex * width + columnIndex := by
            rw [firstLength, Nat.succ_mul]
            omega
          rw [indexEquation]
          simpa using
            induction rowIndex restLengths (by simpa using rowIndexValid)

/-- A valid row and column index retrieve the corresponding entry of a
generic row-major list. -/
theorem rowMajorList_getD {α : Type*}
    (height width : Nat) (entry : Nat → Nat → α) (fallback : α)
    {horizontal vertical : Nat}
    (horizontalValid : horizontal < width)
    (verticalValid : vertical < height) :
    (rowMajorList height width entry).getD
        (vertical * width + horizontal) fallback =
      entry horizontal vertical := by
  unfold rowMajorList
  calc
    _ = ((List.range width).map fun horizontal =>
          entry horizontal vertical).getD horizontal fallback := by
      have compiler := List.getD_flatMap_fixedLength
          (List.range height)
          (fun vertical : Nat =>
            (List.range width).map fun horizontal : Nat =>
              entry horizontal vertical)
          width vertical horizontal fallback
          (by intro item member; simp) (by simpa using verticalValid)
          horizontalValid
      have rangeValid : vertical < (List.range height).length := by
        simpa using verticalValid
      have rowValue : (List.range height)[vertical]'rangeValid = vertical := by
        simp
      rw [rowValue] at compiler
      exact compiler
    _ = _ := by
      rw [List.getD_eq_getElem _ _ (by simpa using horizontalValid)]
      simp

/-- The row-major compiler returns its source lookup at every position in
the stored fundamental domain. -/
theorem PlanarPresentation.finalCellTypes_getD
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {horizontal vertical : Nat}
    (horizontalValid :
      horizontal < presentation.finalNormalizationPeriod)
    (verticalValid :
      vertical < presentation.finalNormalizationPeriod) :
    presentation.finalCellTypes.getD
        (vertical * presentation.finalNormalizationPeriod + horizontal)
        .blank =
      presentation.finalCellTypeAt (horizontal, vertical) := by
  unfold PlanarPresentation.finalCellTypes
  exact rowMajorList_getD _ _ _ _ horizontalValid verticalValid

/-- Reading the compiled drawing at a finite torus position is exactly the
assignment lookup at that position's two representatives. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_get
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (position : presentation.normalizedOrthogonalDrawing.Position) :
    presentation.normalizedOrthogonalDrawing.get position =
      presentation.finalCellTypeAt
        ((position.1.val : Int), (position.2.val : Int)) := by
  have positive := presentation.finalNormalizationPeriod_pos
  have oneLe : 1 ≤ presentation.finalNormalizationPeriod :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt positive)
  have horizontalValid :
      position.1.val < presentation.finalNormalizationPeriod := by
    simpa [PlanarPresentation.normalizedOrthogonalDrawing,
      Nat.sub_add_cancel oneLe] using position.1.isLt
  have verticalValid :
      position.2.val < presentation.finalNormalizationPeriod := by
    simpa [PlanarPresentation.normalizedOrthogonalDrawing,
      Nat.sub_add_cancel oneLe] using position.2.isLt
  unfold PeriodicOrthogonalDrawing.get
  rw [presentation.normalizedOrthogonalDrawing_cellTypes]
  have indexEquation :
      position.2.val *
          (presentation.normalizedOrthogonalDrawing.horizontalPeriodPred + 1) +
        position.1.val =
      position.2.val * presentation.finalNormalizationPeriod +
        position.1.val :=
    congrArg
      (fun width => position.2.val * width + position.1.val)
      presentation.normalizedOrthogonalDrawing_periods.1
  rw [indexEquation]
  exact presentation.finalCellTypes_getD horizontalValid verticalValid

/-- To prove that the compiler's result is well formed, it suffices to
verify matching ports directly on the assignment lookup at every finite
neighbor pair. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_isWellFormed_of_lookup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (matchingPorts :
      ∀ (position : presentation.normalizedOrthogonalDrawing.Position)
        (side : Side),
        (presentation.finalCellTypeAt
            ((position.1.val : Int), (position.2.val : Int))).portColor side =
          (presentation.finalCellTypeAt
            (((presentation.normalizedOrthogonalDrawing.neighbor
                position side).1.val : Int),
              ((presentation.normalizedOrthogonalDrawing.neighbor
                position side).2.val : Int))).portColor side.opposite) :
    presentation.normalizedOrthogonalDrawing.IsWellFormed := by
  constructor
  · have periods := presentation.normalizedOrthogonalDrawing_periods
    rw [presentation.normalizedOrthogonalDrawing_cellTypes]
    rw [presentation.finalCellTypes_length]
    rw [periods.1, periods.2]
    simp [pow_two]
  · intro position side
    rw [presentation.normalizedOrthogonalDrawing_get position]
    rw [presentation.normalizedOrthogonalDrawing_get
      (presentation.normalizedOrthogonalDrawing.neighbor position side)]
    exact matchingPorts position side

/-- Likewise, separation of degree-three cells can be checked directly on
the assignment lookup before packaging it as a drawing. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_verticesSeparated_of_lookup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated :
      ∀ (position : presentation.normalizedOrthogonalDrawing.Position)
        (side : Side),
        (presentation.finalCellTypeAt
            ((position.1.val : Int), (position.2.val : Int))).isVertex = true →
          (presentation.finalCellTypeAt
            (((presentation.normalizedOrthogonalDrawing.neighbor
                position side).1.val : Int),
              ((presentation.normalizedOrthogonalDrawing.neighbor
                position side).2.val : Int))).isVertex = false) :
    presentation.normalizedOrthogonalDrawing.VerticesSeparated := by
  intro position side isVertex
  rw [presentation.normalizedOrthogonalDrawing_get] at isVertex ⊢
  exact separated position side isVertex

/-! ## Geometric points and finite torus positions -/

/-- Reflect geometric coordinates into drawing-row coordinates without yet
choosing a periodic representative. -/
def reflectedLocation (point : Cell) : Cell :=
  (point.1, -point.2)

/-- A genuine geometric unit step becomes the correspondingly named lattice
neighbor after vertical reflection. -/
theorem reflectedLocation_add_step
    (point : Cell) {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    reflectedLocation (Cell.add point direction.step) =
      PeriodicOrthogonalDrawing.latticeNeighbor
        (reflectedLocation point) (Side.ofAxisDirection direction) := by
  rcases point with ⟨horizontal, vertical⟩
  cases direction <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.step,
      Cell.add, reflectedLocation, Side.ofAxisDirection,
      PeriodicOrthogonalDrawing.latticeNeighbor] <;> omega

/-- Project a geometric point directly to the final normalized drawing's
finite torus. -/
def PlanarPresentation.normalizedPositionAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (point : Cell) :
    presentation.normalizedOrthogonalDrawing.Position :=
  presentation.normalizedOrthogonalDrawing.positionAt
    (reflectedLocation point)

/-- Geometric unit steps commute with finite-torus projection. -/
theorem PlanarPresentation.normalizedPositionAt_add_step
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (point : Cell) {direction : AxisDirection}
    (genuine : direction.IsGenuine) :
    presentation.normalizedPositionAt
        (Cell.add point direction.step) =
      presentation.normalizedOrthogonalDrawing.neighbor
        (presentation.normalizedPositionAt point)
        (Side.ofAxisDirection direction) := by
  unfold PlanarPresentation.normalizedPositionAt
  rw [reflectedLocation_add_step point genuine]
  exact PeriodicOrthogonalDrawing.positionAt_latticeNeighbor _ _ _

/-- The finite position's stored integer representatives are precisely
`rasterLocation`. -/
theorem PlanarPresentation.normalizedPositionAt_values
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (point : Cell) :
    (((presentation.normalizedPositionAt point).1.val : Int),
      ((presentation.normalizedPositionAt point).2.val : Int)) =
        rasterLocation presentation.finalNormalizationPeriod point := by
  apply Prod.ext
  · change
      ((PeriodicOrthogonalDrawing.residue point.1
          presentation.normalizedOrthogonalDrawing.horizontalPeriodPred).val :
          Int) =
        point.1 % presentation.finalNormalizationPeriod
    rw [PeriodicOrthogonalDrawing.residue_val_int]
    have periodEquality :
        (presentation.normalizedOrthogonalDrawing.horizontalPeriodPred : Int) +
            1 =
          (presentation.finalNormalizationPeriod : Int) := by
      exact_mod_cast presentation.normalizedOrthogonalDrawing_periods.1
    rw [periodEquality]
  · change
      ((PeriodicOrthogonalDrawing.residue (-point.2)
          presentation.normalizedOrthogonalDrawing.verticalPeriodPred).val :
          Int) =
        (-point.2) % presentation.finalNormalizationPeriod
    rw [PeriodicOrthogonalDrawing.residue_val_int]
    have periodEquality :
        (presentation.normalizedOrthogonalDrawing.verticalPeriodPred : Int) +
            1 =
          (presentation.finalNormalizationPeriod : Int) := by
      exact_mod_cast presentation.normalizedOrthogonalDrawing_periods.2
    rw [periodEquality]

/-- Reading the compiled drawing at a projected geometric point uses exactly
the rasterized assignment key. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_get_normalizedPositionAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (point : Cell) :
    presentation.normalizedOrthogonalDrawing.get
        (presentation.normalizedPositionAt point) =
      presentation.finalCellTypeAt
        (rasterLocation presentation.finalNormalizationPeriod point) := by
  rw [presentation.normalizedOrthogonalDrawing_get]
  rw [presentation.normalizedPositionAt_values]

end PeriodicThreeDM
end LeanTrominoes
