/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetReductionComputability

/-!
# Strip specialization of tromino gadget substitution

The same finite `6 × 6` block motif used by the two-dimensional gadget
reduction can be repeated only horizontally.  This file packages that motif
as a well-formed `PeriodicStrip`, identifies its carrier exactly, and proves
the construction computable.
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

open Computability

/-- Compile a normalized periodic drawing fundamental domain to a horizontally
periodic finite-height tromino region. -/
def periodicStrip (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : PeriodicStrip where
  width := 6 * drawing.verticalPeriod
  period := 6 * drawing.horizontalPeriod
  motif := expandedMotif tromino drawing

theorem periodicStrip_width (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicStrip tromino).width =
      6 * drawing.verticalPeriod :=
  rfl

theorem periodicStrip_period (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicStrip tromino).period =
      6 * drawing.horizontalPeriod :=
  rfl

/-- Every expanded gadget pixel lies in the selected strip fundamental
rectangle. -/
theorem expandedMotif_mem_fundamentalDomain (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (cell : Cell)
    (membership : cell ∈ expandedMotif tromino drawing) :
    (drawing.periodicStrip tromino).InFundamentalDomain cell := by
  simp only [expandedMotif, List.mem_flatMap] at membership
  obtain ⟨horizontal, -, vertical, -, membership⟩ := membership
  simp only [expandedBlockPixels, List.mem_map] at membership
  obtain ⟨pixel, pixelMembership, rfl⟩ := membership
  have pixelInRegion :
      pixel ∈ (orthogonalCellGadget tromino (drawing.get (horizontal, vertical))).region := by
    simpa [orthogonalCellGadget, paperGadget] using pixelMembership
  have pixelInWindow :=
    orthogonalCellGadget_wellFormed tromino
      (drawing.get (horizontal, vertical)) pixelInRegion
  simp only [Gadget.window, orthogonalCellGadget, paperGadget] at pixelInWindow
  rw [mem_rectangleCells_iff] at pixelInWindow
  unfold PeriodicStrip.InFundamentalDomain
  change
    0 ≤ 6 * (horizontal.val : Int) + pixel.1 ∧
      6 * (horizontal.val : Int) + pixel.1 <
        ((6 * drawing.horizontalPeriod : Nat) : Int) ∧
      0 ≤ 6 * (vertical.val : Int) + pixel.2 ∧
      6 * (vertical.val : Int) + pixel.2 <
        ((6 * drawing.verticalPeriod : Nat) : Int)
  simp only [horizontalPeriod, verticalPeriod, Nat.cast_mul, Nat.cast_add,
    Nat.cast_ofNat]
  have horizontalBound := horizontal.isLt
  have verticalBound := vertical.isLt
  omega

/-- Gadget substitution always produces a valid finite strip presentation. -/
theorem periodicStrip_isWellFormed (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicStrip tromino).IsWellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simp [periodicStrip, verticalPeriod]
  · simp [periodicStrip, horizontalPeriod]
  · intro cell membership
    exact expandedMotif_mem_fundamentalDomain tromino drawing cell membership

/-- Set-theoretic horizontal expansion of the finite gadget motif. -/
def expandedStripCarrier (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : Set Cell :=
  { cell | ∃ position : drawing.Position,
      ∃ pixel ∈ orthogonalCellPixels tromino (drawing.get position),
        ∃ horizontal : Int,
          cell = Cell.add
            (Cell.add
              (blockOrigin position.1.val position.2.val) pixel)
            (Cell.scale horizontal
              (((6 * drawing.horizontalPeriod : Nat) : Int), 0)) }

/-- The carrier of the strip presentation is exactly the horizontal expansion
of all gadget blocks in one finite vertical drawing domain. -/
theorem periodicStrip_carrier_eq (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    (drawing.periodicStrip tromino).carrier =
      drawing.expandedStripCarrier tromino := by
  ext cell
  constructor
  · rintro ⟨verticalNonnegative, verticalBound, base, baseMembership,
      horizontal, equality⟩
    simp only [periodicStrip, expandedMotif, List.mem_flatMap] at baseMembership
    obtain ⟨horizontalIndex, -, verticalIndex, -, baseMembership⟩ :=
      baseMembership
    simp only [expandedBlockPixels, List.mem_map] at baseMembership
    obtain ⟨pixel, pixelMembership, rfl⟩ := baseMembership
    exact ⟨(horizontalIndex, verticalIndex), pixel, pixelMembership,
      horizontal, equality⟩
  · rintro ⟨⟨horizontalIndex, verticalIndex⟩, pixel,
      pixelMembership, horizontal, equality⟩
    let base := Cell.add
      (blockOrigin horizontalIndex.val verticalIndex.val) pixel
    have baseMembership : base ∈ expandedMotif tromino drawing := by
      simp only [expandedMotif, List.mem_flatMap]
      refine ⟨horizontalIndex, List.mem_finRange horizontalIndex,
        verticalIndex, List.mem_finRange verticalIndex, ?_⟩
      simp only [expandedBlockPixels, List.mem_map]
      exact ⟨pixel, pixelMembership, rfl⟩
    have baseBounds :=
      expandedMotif_mem_fundamentalDomain tromino drawing base baseMembership
    have verticalEquality := congrArg Prod.snd equality
    have cellVertical : cell.2 = base.2 := by
      simpa [base, blockOrigin, Cell.add, Cell.scale] using verticalEquality
    refine ⟨?_, ?_, base, baseMembership, horizontal, equality⟩
    · rw [cellVertical]
      exact baseBounds.2.2.1
    · rw [cellVertical]
      exact baseBounds.2.2.2

/-- Natural-range implementation used for computability. -/
def computablePeriodicStrip (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : PeriodicStrip where
  width := 6 * drawing.verticalPeriod
  period := 6 * drawing.horizontalPeriod
  motif := drawing.computableExpandedMotif tromino

theorem computablePeriodicStrip_eq (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    drawing.computablePeriodicStrip tromino =
      drawing.periodicStrip tromino := by
  apply PeriodicStrip.equivData.injective
  simp [PeriodicStrip.equivData, computablePeriodicStrip, periodicStrip,
    drawing.computableExpandedMotif_eq tromino]

theorem computablePeriodicStrip_primrec (tromino : Tromino) :
    Primrec fun drawing : PeriodicOrthogonalDrawing =>
      drawing.computablePeriodicStrip tromino := by
  have width : Primrec fun drawing : PeriodicOrthogonalDrawing =>
      6 * drawing.verticalPeriod :=
    Primrec.nat_mul.comp (Primrec.const 6)
      periodicOrthogonalDrawing_verticalPeriod_primrec
  have period : Primrec fun drawing : PeriodicOrthogonalDrawing =>
      6 * drawing.horizontalPeriod :=
    Primrec.nat_mul.comp (Primrec.const 6)
      periodicOrthogonalDrawing_horizontalPeriod_primrec
  have data : Primrec fun drawing : PeriodicOrthogonalDrawing =>
      (6 * drawing.verticalPeriod,
        6 * drawing.horizontalPeriod,
        drawing.computableExpandedMotif tromino) :=
    Primrec.pair width
      (Primrec.pair period (computableExpandedMotif_primrec tromino))
  exact (Primrec.of_equiv_symm :
    Primrec PeriodicStrip.equivData.symm).comp data

theorem periodicStrip_primrec (tromino : Tromino) :
    Primrec fun drawing : PeriodicOrthogonalDrawing =>
      drawing.periodicStrip tromino :=
  (computablePeriodicStrip_primrec tromino).of_eq fun drawing =>
    drawing.computablePeriodicStrip_eq tromino

theorem periodicStrip_computable (tromino : Tromino) :
    Computable fun drawing : PeriodicOrthogonalDrawing =>
      drawing.periodicStrip tromino :=
  (periodicStrip_primrec tromino).to_comp

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
