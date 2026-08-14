/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetStripSubstitution
import LeanTrominoes.GadgetBehavior

/-!
# Stacking a gadget-strip tiling into the periodic plane

The doubly periodic gadget carrier is the disjoint vertical stack of copies of
its horizontally periodic strip carrier.  Consequently, any strip tiling can
be translated into every vertical band to obtain a plane tiling.  This gives
the unconditional soundness direction needed by the 1.5D reduction.
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- Expanded vertical period of one substituted drawing domain. -/
def verticalPixelPeriod (drawing : PeriodicOrthogonalDrawing) : Int :=
  6 * (drawing.verticalPeriod : Int)

/-- Translation from the base strip to one vertical copy. -/
def verticalOffset (drawing : PeriodicOrthogonalDrawing)
    (index : Int) : Cell :=
  (0, index * drawing.verticalPixelPeriod)

theorem verticalPixelPeriod_pos (drawing : PeriodicOrthogonalDrawing) :
    0 < drawing.verticalPixelPeriod := by
  simp [verticalPixelPeriod, verticalPeriod]

/-- A point has a unique vertical-band index when its residual height lies in
one half-open period interval. -/
theorem verticalBandIndex_unique {height firstY secondY firstIndex secondIndex : Int}
    (heightPositive : 0 < height)
    (firstNonnegative : 0 ≤ firstY) (firstBelow : firstY < height)
    (secondNonnegative : 0 ≤ secondY) (secondBelow : secondY < height)
    (equality : firstY + firstIndex * height =
      secondY + secondIndex * height) :
    firstIndex = secondIndex := by
  by_contra distinct
  rcases lt_or_gt_of_ne distinct with less | greater
  · have nextLe : firstIndex + 1 ≤ secondIndex := by omega
    have scaled : (firstIndex + 1) * height ≤ secondIndex * height :=
      Int.mul_le_mul_of_nonneg_right nextLe (by omega)
    nlinarith
  · have nextLe : secondIndex + 1 ≤ firstIndex := by omega
    have scaled : (secondIndex + 1) * height ≤ firstIndex * height :=
      Int.mul_le_mul_of_nonneg_right nextLe (by omega)
    nlinarith

/-- The plane carrier is exactly the vertical stack of translated strip
carriers. -/
theorem mem_periodicRegion_carrier_iff_verticalStrip
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) (cell : Cell) :
    cell ∈ (drawing.periodicRegion tromino).carrier ↔
      ∃ index : Int, ∃ source ∈ (drawing.periodicStrip tromino).carrier,
        cell = Cell.add (drawing.verticalOffset index) source := by
  rw [periodicRegion_carrier_eq, periodicStrip_carrier_eq]
  constructor
  · rintro ⟨position, pixel, pixelMembership, horizontal, vertical,
      equality⟩
    let source := Cell.add
      (Cell.add (blockOrigin position.1.val position.2.val) pixel)
      (Cell.scale horizontal
        ((6 * (drawing.horizontalPeriod : Int), 0) : Cell))
    refine ⟨vertical, source, ?_, ?_⟩
    · exact ⟨position, pixel, pixelMembership, horizontal, rfl⟩
    · rw [equality]
      apply Prod.ext
      all_goals
        simp [source, verticalOffset, verticalPixelPeriod, Cell.add,
          Cell.scale]
      all_goals ring
  · rintro ⟨vertical, source,
      ⟨position, pixel, pixelMembership, horizontal, sourceEquality⟩,
      equality⟩
    refine ⟨position, pixel, pixelMembership, horizontal, vertical, ?_⟩
    rw [equality, sourceEquality]
    apply Prod.ext
    all_goals
      simp [verticalOffset, verticalPixelPeriod, Cell.add, Cell.scale]
    all_goals ring

/-- The base strip is exactly the part of the plane carrier in one half-open
vertical period band. -/
theorem mem_periodicStrip_carrier_iff_region_and_verticalBounds
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) (cell : Cell) :
    cell ∈ (drawing.periodicStrip tromino).carrier ↔
      cell ∈ (drawing.periodicRegion tromino).carrier ∧
        0 ≤ cell.2 ∧ cell.2 < drawing.verticalPixelPeriod := by
  constructor
  · intro membership
    refine ⟨(mem_periodicRegion_carrier_iff_verticalStrip
      tromino drawing cell).mpr ⟨0, cell, membership, ?_⟩,
      membership.1, ?_⟩
    · simp [verticalOffset, verticalPixelPeriod, Cell.add]
    · simpa [periodicStrip, verticalPixelPeriod] using membership.2.1
  · rintro ⟨planeMembership, cellNonnegative, cellBelow⟩
    obtain ⟨index, source, sourceMembership, equality⟩ :=
      (mem_periodicRegion_carrier_iff_verticalStrip
        tromino drawing cell).mp planeMembership
    have sourceBelow : source.2 < drawing.verticalPixelPeriod := by
      simpa [periodicStrip, verticalPixelPeriod] using sourceMembership.2.1
    have verticalEquality :
        cell.2 + 0 * drawing.verticalPixelPeriod =
          source.2 + index * drawing.verticalPixelPeriod := by
      have projected := congrArg Prod.snd equality
      simp [verticalOffset, Cell.add] at projected ⊢
      rw [projected]
      ring
    have indexZero : (0 : Int) = index :=
      verticalBandIndex_unique
        drawing.verticalPixelPeriod_pos
        cellNonnegative cellBelow sourceMembership.1 sourceBelow
        verticalEquality
    subst index
    have cellEquality : cell = source := by
      simpa [verticalOffset, verticalPixelPeriod, Cell.add] using equality
    rw [cellEquality]
    exact sourceMembership

/-- Translate every placement of one strip tiling into every vertical copy. -/
def stackedPlacements (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit)) : Set (Placement Unit) :=
  { placement | ∃ index : Int, ∃ source ∈ placements,
      placement = translatePlacement (drawing.verticalOffset index) source }

/-- Repeating a strip tiling vertically tiles the corresponding doubly
periodic gadget carrier. -/
theorem periodicRegion_tileable_of_periodicStrip_tileable
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (tileable : tromino.Tileable (drawing.periodicStrip tromino).carrier) :
    tromino.Tileable (drawing.periodicRegion tromino).carrier := by
  obtain ⟨placements, tiling⟩ := tileable
  refine ⟨drawing.stackedPlacements placements, ?_⟩
  constructor
  · intro placement placementMembership cell cellMembership
    obtain ⟨index, sourcePlacement, sourcePlacementMembership, rfl⟩ :=
      placementMembership
    rw [translatePlacement_cells] at cellMembership
    obtain ⟨sourceCell, sourceCellMembership, sourceCellEquality⟩ :=
      Finset.mem_image.mp cellMembership
    have sourceInStrip := tiling.tilesInside sourcePlacement
      sourcePlacementMembership sourceCell sourceCellMembership
    apply (mem_periodicRegion_carrier_iff_verticalStrip
      tromino drawing cell).mpr
    exact ⟨index, sourceCell, sourceInStrip, sourceCellEquality.symm⟩
  · intro cell cellMembership
    obtain ⟨index, sourceCell, sourceInStrip, cellEquality⟩ :=
      (mem_periodicRegion_carrier_iff_verticalStrip
        tromino drawing cell).mp cellMembership
    obtain ⟨sourcePlacement,
        ⟨sourcePlacementMembership, sourcePlacementCovers⟩,
        sourceUnique⟩ := tiling.uniqueCover sourceCell sourceInStrip
    let placement :=
      translatePlacement (drawing.verticalOffset index) sourcePlacement
    refine ⟨placement, ⟨?_, ?_⟩, ?_⟩
    · exact ⟨index, sourcePlacement, sourcePlacementMembership, rfl⟩
    · unfold placement
      rw [translatePlacement_cells, cellEquality]
      exact (add_mem_translateFootprint_iff
        (drawing.verticalOffset index) sourceCell
        (sourcePlacement.cells fun _ : Unit => tromino.cells)).mpr
          sourcePlacementCovers
    · intro other ⟨otherMembership, otherCovers⟩
      obtain ⟨otherIndex, otherSourcePlacement,
          otherSourcePlacementMembership, otherEquality⟩ := otherMembership
      subst other
      rw [translatePlacement_cells] at otherCovers
      obtain ⟨otherSourceCell, otherSourceCovers, otherCellEquality⟩ :=
        Finset.mem_image.mp otherCovers
      have otherSourceInStrip := tiling.tilesInside otherSourcePlacement
        otherSourcePlacementMembership otherSourceCell otherSourceCovers
      have sourceBounds := sourceInStrip
      have otherBounds := otherSourceInStrip
      have verticalEquality :
          sourceCell.2 + index * drawing.verticalPixelPeriod =
            otherSourceCell.2 +
              otherIndex * drawing.verticalPixelPeriod := by
        have first := congrArg Prod.snd cellEquality
        have second := congrArg Prod.snd otherCellEquality
        simp only [verticalOffset, Cell.add] at first second
        omega
      have indexEquality : index = otherIndex :=
        verticalBandIndex_unique
          (drawing.verticalPixelPeriod_pos)
          sourceBounds.1 sourceBounds.2.1
          otherBounds.1 otherBounds.2.1
          (by simpa [periodicStrip, verticalPixelPeriod] using verticalEquality)
      subst otherIndex
      have sourceCellEquality : sourceCell = otherSourceCell := by
        apply Cell.add_left_injective (drawing.verticalOffset index)
        exact cellEquality.symm.trans otherCellEquality.symm
      subst otherSourceCell
      have sourcePlacementEquality := sourceUnique otherSourcePlacement
        ⟨otherSourcePlacementMembership, otherSourceCovers⟩
      subst otherSourcePlacement
      rfl

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
