/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalDrawing
import LeanTrominoes.Periodic
import Mathlib.Data.List.FinRange

/-!
# Substitution of normalized drawing cells by tromino gadgets

Each cell of a normalized drawing is replaced by its `6 × 6` Figure 11 or 12
pixel mask.  This file defines the finite motif produced by that substitution
and packages it as the periodic-region input of Theorem 5.2.
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- The positive horizontal period of the finite drawing domain. -/
def horizontalPeriod (drawing : PeriodicOrthogonalDrawing) : Nat :=
  drawing.horizontalPeriodPred + 1

/-- The positive vertical period of the finite drawing domain. -/
def verticalPeriod (drawing : PeriodicOrthogonalDrawing) : Nat :=
  drawing.verticalPeriodPred + 1

/-- Origin of a `6 × 6` gadget block in the expanded motif. -/
def blockOrigin (horizontal vertical : Nat) : Cell :=
  (6 * (horizontal : Int), 6 * (vertical : Int))

/-- Translate every local paper pixel into one block of the expanded motif. -/
def expandedBlockPixels (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (position : drawing.Position) :
    List Cell :=
  (orthogonalCellPixels tromino (drawing.get position)).map fun pixel =>
    Cell.add (blockOrigin position.1.val position.2.val) pixel

/-- The finite motif obtained by substituting every drawing cell with its
Figure 11 or 12 gadget. -/
def expandedMotif (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : List Cell :=
  (List.finRange drawing.horizontalPeriod).flatMap fun horizontal =>
    (List.finRange drawing.verticalPeriod).flatMap fun vertical =>
      expandedBlockPixels tromino drawing (horizontal, vertical)

/-- Compile a normalized periodic drawing to the periodic subset tiled in the
hardness reduction. -/
def periodicRegion (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : PeriodicRegion where
  motif := expandedMotif tromino drawing
  period₁ := (6 * (drawing.horizontalPeriod : Int), 0)
  period₂ := (0, 6 * (drawing.verticalPeriod : Int))

theorem periodicRegion_determinant (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicRegion tromino).determinant =
      36 * (drawing.horizontalPeriod : Int) *
        (drawing.verticalPeriod : Int) := by
  simp [periodicRegion, PeriodicRegion.determinant]
  ring

/-- The compiled region always has two independent period vectors. -/
theorem periodicRegion_fullRank (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicRegion tromino).IsFullRank := by
  rw [PeriodicRegion.IsFullRank, periodicRegion_determinant]
  have horizontalPositive : (0 : Int) < drawing.horizontalPeriod := by
    simp [horizontalPeriod]
  have verticalPositive : (0 : Int) < drawing.verticalPeriod := by
    simp [verticalPeriod]
  positivity

/-- The set-theoretic infinite expansion: choose a block in the finite torus,
then translate its local mask by arbitrary whole drawing periods. -/
def expandedCarrier (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : Set Cell :=
  { cell | ∃ position : drawing.Position,
      ∃ pixel ∈ orthogonalCellPixels tromino (drawing.get position),
        ∃ horizontal vertical : Int,
          cell = Cell.add
            (Cell.add
              (Cell.add
                (blockOrigin position.1.val position.2.val) pixel)
              (Cell.scale horizontal
                ((6 * (drawing.horizontalPeriod : Int), 0) : Cell)))
            (Cell.scale vertical
              ((0, 6 * (drawing.verticalPeriod : Int)) : Cell)) }

/-- The carrier of the compiled finite presentation is exactly the infinite
periodic union of its substituted gadget blocks. -/
theorem periodicRegion_carrier_eq (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicRegion tromino).carrier =
      drawing.expandedCarrier tromino := by
  ext cell
  constructor
  · rintro ⟨base, baseMember, horizontal, vertical, equality⟩
    change base ∈ expandedMotif tromino drawing at baseMember
    simp only [periodicRegion] at equality
    simp only [expandedMotif, List.mem_flatMap] at baseMember
    obtain ⟨horizontalIndex, _, verticalIndex, _, baseMember⟩ := baseMember
    simp only [expandedBlockPixels, List.mem_map] at baseMember
    obtain ⟨pixel, pixelMember, pixelEquality⟩ := baseMember
    subst base
    exact ⟨(horizontalIndex, verticalIndex), pixel, pixelMember,
      horizontal, vertical, equality⟩
  · rintro ⟨⟨horizontalIndex, verticalIndex⟩, pixel, pixelMember,
      horizontal, vertical, equality⟩
    refine ⟨Cell.add
        (blockOrigin horizontalIndex.val verticalIndex.val) pixel, ?_,
      horizontal, vertical, ?_⟩
    · simp only [periodicRegion, expandedMotif, List.mem_flatMap]
      refine ⟨horizontalIndex, List.mem_finRange horizontalIndex,
        verticalIndex, List.mem_finRange verticalIndex, ?_⟩
      simp only [expandedBlockPixels, List.mem_map]
      exact ⟨pixel, pixelMember, rfl⟩
    · simpa only [periodicRegion] using equality

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
