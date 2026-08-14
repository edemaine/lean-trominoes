/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetStripStacking

/-!
# Gluing vertically closed gadget assignments on a strip

Restrict the infinite gadget-block atlas to one finite vertical drawing band,
using empty local regions outside it.  A geometric closure condition at the
two horizontal boundaries is exactly what is needed for the existing
footprint-atlas theorem to glue all retained local states into a strip tiling.
-/

namespace LeanTrominoes
namespace Gadget
namespace PeriodicOrthogonalDrawing

/-- Drawing-block indices retained in the base strip. -/
def IsStripBlock (drawing : PeriodicOrthogonalDrawing)
    (location : Cell) : Prop :=
  0 ≤ location.2 ∧ location.2 < (drawing.verticalPeriod : Int)

instance (drawing : PeriodicOrthogonalDrawing) (location : Cell) :
    Decidable (drawing.IsStripBlock location) := by
  unfold IsStripBlock
  infer_instance

/-- Keep a gadget region only in the selected finite vertical block band. -/
def stripBlockRegion (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (location : Cell) : Finset Cell :=
  if drawing.IsStripBlock location then
    drawingBlockRegion tromino drawing location
  else
    ∅

/-- Keep a selected local footprint family only in the strip block band. -/
def stripBlockFootprints (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell) : Finset (Finset Cell) :=
  if drawing.IsStripBlock location then
    drawingBlockFootprints tromino drawing assignment location
  else
    ∅

/-- No selected footprint based in the retained band meets a block window
outside it. -/
def IsVerticallyClosed (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  ∀ first second footprint,
    drawing.IsStripBlock first →
      ¬ drawing.IsStripBlock second →
      footprint ∈ drawingBlockFootprints tromino drawing assignment first →
      ¬ ∃ cell ∈ latticeBlockWindow second, cell ∈ footprint

/-- The union of retained block regions is exactly the compiled strip
carrier. -/
theorem stripBlockRegion_carrier_eq (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    ({ cell | ∃ location, cell ∈ stripBlockRegion tromino drawing location } :
        Set Cell) =
      (drawing.periodicStrip tromino).carrier := by
  ext cell
  constructor
  · rintro ⟨location, membership⟩
    by_cases retained : drawing.IsStripBlock location
    · simp only [stripBlockRegion, if_pos retained] at membership
      have planeMembership :
          cell ∈ (drawing.periodicRegion tromino).carrier := by
        rw [periodicRegion_carrier_eq,
          ← liftedGadgetCarrier_eq_expandedCarrier]
        exact ⟨location, membership⟩
      have windowMembership :=
        drawingBlockRegion_subset_window tromino drawing location membership
      obtain ⟨localCell, localMembership, localEquality⟩ :=
        Finset.mem_image.mp windowMembership
      have localBounds :=
        (mem_rectangleCells_iff 6 6 localCell).mp localMembership
      have verticalEquality := congrArg Prod.snd localEquality
      unfold IsStripBlock at retained
      apply (mem_periodicStrip_carrier_iff_region_and_verticalBounds
        tromino drawing cell).mpr
      refine ⟨planeMembership, ?_, ?_⟩
      · simp only [latticeBlockOrigin, Cell.add] at verticalEquality
        omega
      · simp only [latticeBlockOrigin, Cell.add] at verticalEquality
        unfold verticalPixelPeriod
        omega
    · simp [stripBlockRegion, retained] at membership
  · intro stripMembership
    have characterized :=
      (mem_periodicStrip_carrier_iff_region_and_verticalBounds
        tromino drawing cell).mp stripMembership
    have planeMembership := characterized.1
    rw [periodicRegion_carrier_eq,
      ← liftedGadgetCarrier_eq_expandedCarrier] at planeMembership
    obtain ⟨location, regionMembership⟩ := planeMembership
    have windowMembership :=
      drawingBlockRegion_subset_window tromino drawing location regionMembership
    obtain ⟨localCell, localMembership, localEquality⟩ :=
      Finset.mem_image.mp windowMembership
    have localBounds :=
      (mem_rectangleCells_iff 6 6 localCell).mp localMembership
    have verticalEquality := congrArg Prod.snd localEquality
    have retained : drawing.IsStripBlock location := by
      unfold IsStripBlock
      unfold verticalPixelPeriod at characterized
      simp only [latticeBlockOrigin, Cell.add] at verticalEquality
      omega
    exact ⟨location, by
      simpa [stripBlockRegion, retained] using regionMembership⟩

/-- A locally tiled, coherent, vertically closed assignment gives a footprint
atlas whose target carrier is the gadget strip. -/
def stripFootprintAtlas (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (closed : IsVerticallyClosed tromino drawing assignment) :
    FootprintAtlas tromino latticeBlockWindow
      (stripBlockRegion tromino drawing) where
  footprints := stripBlockFootprints tromino drawing assignment
  regionInside := by
    intro location
    by_cases retained : drawing.IsStripBlock location
    · simp only [stripBlockRegion, if_pos retained]
      exact drawingBlockRegion_subset_window tromino drawing location
    · simp [stripBlockRegion, retained]
  windowsCover := latticeBlockWindows_cover
  localTiling := by
    intro location
    by_cases retained : drawing.IsStripBlock location
    · have localPlacementTiling :=
        (mem_exactCellTilings_iff tromino (drawing.getAt location)
          (assignment location)).mp (locallyTiled location)
      have localFootprintTiling :=
        localPlacementTiling.isWindowFootprintTiling
      simpa only [stripBlockRegion, stripBlockFootprints, if_pos retained,
        drawingBlockRegion, drawingBlockFootprints, latticeBlockWindow,
        latticeBlockRegion, orthogonalCellGadget, paperGadget, Gadget.window]
        using localFootprintTiling.translate (latticeBlockOrigin location)
    · simp only [stripBlockRegion, stripBlockFootprints, if_neg retained]
      refine
        { isFootprint := ?_
          meetsWindow := ?_
          visibleInside := ?_
          uniqueCover := ?_ }
      · simp
      · simp
      · simp
      · simp
  coherent := by
    intro first second footprint firstMembership meetsSecond
    by_cases firstRetained : drawing.IsStripBlock first
    · simp only [stripBlockFootprints, if_pos firstRetained] at firstMembership
      by_cases secondRetained : drawing.IsStripBlock second
      · simp only [stripBlockFootprints, if_pos secondRetained]
        exact coherent first second footprint firstMembership meetsSecond
      · exact (closed first second footprint firstRetained secondRetained
          firstMembership meetsSecond).elim
    · simp [stripBlockFootprints, firstRetained] at firstMembership

/-- Vertically closed compatible local states tile the compiled strip. -/
theorem periodicStrip_tileable_of_closed_assignment
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (closed : IsVerticallyClosed tromino drawing assignment) :
    tromino.Tileable (drawing.periodicStrip tromino).carrier := by
  let atlas := stripFootprintAtlas tromino drawing assignment locallyTiled
    coherent closed
  rw [← stripBlockRegion_carrier_eq tromino drawing]
  exact atlas.tileable

/-- Port compatibility plus vertical closure is sufficient for strip
tileability. -/
theorem periodicStrip_tileable_of_portCompatible_closed
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (compatible : IsPortCompatible tromino drawing assignment)
    (closed : IsVerticallyClosed tromino drawing assignment) :
    tromino.Tileable (drawing.periodicStrip tromino).carrier :=
  periodicStrip_tileable_of_closed_assignment tromino drawing assignment
    locallyTiled
    (isGeometricallyCoherent_of_portCompatible tromino drawing assignment
      locallyTiled compatible)
    closed

end PeriodicOrthogonalDrawing
end Gadget
end LeanTrominoes
