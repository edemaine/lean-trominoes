import LeanTrominoes.GadgetAssembly
import LeanTrominoes.GadgetSubstitution

/-!
# Infinite compatible assignments of local gadget tilings

The substitution proof factors through a finite-state constraint system on
the infinite lifted drawing.  At every drawing cell we select one local tiling
certified by exact-cover search. Neighboring selections must have identical
normalized geometric port states along their shared side.
-/

namespace LeanTrominoes
namespace Gadget

/-- Verified exact-cover enumeration specialized to one cell of the complete
Figure 11/12 gadget alphabet. -/
def exactCellTilings (tromino : Tromino) (cellType : OrthogonalCellType) :
    List (Finset (Placement Unit)) :=
  exactWindowTilings tromino (orthogonalCellGadget tromino cellType)
    (orthogonalCellPixels tromino cellType)

/-- Membership in the executable local-state list is exactly the semantic
open-window tiling predicate. -/
theorem mem_exactCellTilings_iff (tromino : Tromino)
    (cellType : OrthogonalCellType) (placements : Finset (Placement Unit)) :
    placements ∈ exactCellTilings tromino cellType ↔
      IsWindowTiling tromino
        (orthogonalCellGadget tromino cellType).window
        (orthogonalCellGadget tromino cellType).region placements := by
  exact mem_exactWindowTilings_iff tromino
    (orthogonalCellGadget tromino cellType)
    (orthogonalCellGadget_wellFormed tromino cellType)
    (orthogonalCellPixels tromino cellType) rfl placements

/-- The four-port behavior of all verified local tilings of one drawing-cell
type. -/
def exactCellPortConfigurations (tromino : Tromino)
    (cellType : OrthogonalCellType) : Finset PortConfiguration :=
  exactPortConfigurations tromino (orthogonalCellGadget tromino cellType)
    (orthogonalCellPixels tromino cellType)

/-- The executable port behavior has the expected semantic interpretation. -/
theorem mem_exactCellPortConfigurations_iff (tromino : Tromino)
    (cellType : OrthogonalCellType) (configuration : PortConfiguration) :
    configuration ∈ exactCellPortConfigurations tromino cellType ↔
      ∃ placements,
        IsWindowTiling tromino
          (orthogonalCellGadget tromino cellType).window
          (orthogonalCellGadget tromino cellType).region placements ∧
        portConfiguration tromino
          (orthogonalCellGadget tromino cellType) placements = configuration := by
  exact mem_exactPortConfigurations_iff tromino
    (orthogonalCellGadget tromino cellType)
    (orthogonalCellGadget_wellFormed tromino cellType)
    (orthogonalCellPixels tromino cellType) rfl configuration

/-- One local placement selection at every cell of the infinite lifted
drawing. Placements use coordinates relative to their own `6 × 6` block. -/
abbrev LocalTilingAssignment (_tromino : Tromino)
    (_drawing : PeriodicOrthogonalDrawing) :=
  Cell → Finset (Placement Unit)

/-- Every selected local state is one of the states returned by verified
exact-cover search. -/
def IsLocallyTiled (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  ∀ location,
    assignment location ∈ exactCellTilings tromino (drawing.getAt location)

/-- Neighboring local tilings retain exactly the same geometric tromino
footprints at every shared block boundary. -/
def IsPortCompatible (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  (∀ location,
    HorizontallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location))
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .east)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .east)))) ∧
  ∀ location,
    VerticallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location))
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .south)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
      )

/-- The intermediate infinite finite-state system implemented by the tromino
gadget library. -/
def HasCompatibleGadgetTiling (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : Prop :=
  ∃ assignment : LocalTilingAssignment tromino drawing,
    IsLocallyTiled tromino drawing assignment ∧
      IsPortCompatible tromino drawing assignment

/-! ## Geometric realization on the lattice-block atlas -/

/-- The paper mask translated into the `6 × 6` block at one cell of the
infinite lifted drawing. -/
def drawingBlockRegion (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (location : Cell) : Finset Cell :=
  latticeBlockRegion location
    (orthogonalCellPixels tromino (drawing.getAt location)).toFinset

/-- The local selected footprints translated to their global lattice
coordinates. -/
def drawingBlockFootprints (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell) : Finset (Finset Cell) :=
  translateFootprints (latticeBlockOrigin location)
    (windowFootprints tromino (assignment location))

/-- Port agreement must ultimately imply this geometric condition: every
selected tromino footprint occurs in every lattice block that it meets. -/
def IsGeometricallyCoherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  ∀ first second footprint,
    footprint ∈ drawingBlockFootprints tromino drawing assignment first →
      (∃ cell ∈ latticeBlockWindow second, cell ∈ footprint) →
        footprint ∈ drawingBlockFootprints tromino drawing assignment second

/-- The infinite union of all translated Figure 11/12 pixel masks. -/
def liftedGadgetCarrier (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : Set Cell :=
  { cell | ∃ location, cell ∈ drawingBlockRegion tromino drawing location }

/-- The block-atlas carrier is exactly the infinite carrier specified by the
finite periodic-region compilation. -/
theorem liftedGadgetCarrier_eq_expandedCarrier (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    liftedGadgetCarrier tromino drawing = drawing.expandedCarrier tromino := by
  ext cell
  constructor
  · rintro ⟨location, cellMember⟩
    obtain ⟨pixel, pixelMember, pixelEquality⟩ :=
      Finset.mem_image.mp cellMember
    let position := drawing.positionAt location
    refine ⟨position, pixel, ?_,
      location.1 / (drawing.horizontalPeriod : Int),
      location.2 / (drawing.verticalPeriod : Int), ?_⟩
    · simpa only [drawingBlockRegion, latticeBlockRegion, List.mem_toFinset,
        PeriodicOrthogonalDrawing.getAt, position] using pixelMember
    · have horizontalDecomposition := Int.emod_add_mul_ediv location.1
        (drawing.horizontalPeriod : Int)
      have verticalDecomposition := Int.emod_add_mul_ediv location.2
        (drawing.verticalPeriod : Int)
      have horizontalResidue :=
        PeriodicOrthogonalDrawing.residue_val_int location.1
          drawing.horizontalPeriodPred
      have verticalResidue :=
        PeriodicOrthogonalDrawing.residue_val_int location.2
          drawing.verticalPeriodPred
      have pixelHorizontal := congrArg Prod.fst pixelEquality
      have pixelVertical := congrArg Prod.snd pixelEquality
      apply Prod.ext
      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin,
          PeriodicOrthogonalDrawing.positionAt,
          PeriodicOrthogonalDrawing.horizontalPeriod,
          PeriodicOrthogonalDrawing.verticalPeriod, position] at pixelHorizontal horizontalDecomposition horizontalResidue ⊢
        rw [horizontalResidue]
        simp only [Nat.cast_add, Nat.cast_one] at horizontalDecomposition ⊢
        ring_nf at horizontalDecomposition pixelHorizontal ⊢
        linarith
      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin,
          PeriodicOrthogonalDrawing.positionAt,
          PeriodicOrthogonalDrawing.horizontalPeriod,
          PeriodicOrthogonalDrawing.verticalPeriod, position] at pixelVertical verticalDecomposition verticalResidue ⊢
        rw [verticalResidue]
        simp only [Nat.cast_add, Nat.cast_one] at verticalDecomposition ⊢
        ring_nf at verticalDecomposition pixelVertical ⊢
        linarith
  · rintro ⟨position, pixel, pixelMember, horizontal, vertical, equality⟩
    let location : Cell :=
      ((position.1.val : Int) +
          horizontal * (drawing.horizontalPeriod : Int),
        (position.2.val : Int) +
          vertical * (drawing.verticalPeriod : Int))
    refine ⟨location, Finset.mem_image.mpr ⟨pixel, ?_, ?_⟩⟩
    · have positionEquality : drawing.positionAt location = position := by
        simpa only [location,
          PeriodicOrthogonalDrawing.horizontalPeriod,
          PeriodicOrthogonalDrawing.verticalPeriod, Nat.cast_add,
          Nat.cast_one] using
            drawing.positionAt_add_periods position horizontal vertical
      simpa only [drawingBlockRegion, latticeBlockRegion, List.mem_toFinset,
        PeriodicOrthogonalDrawing.getAt, positionEquality] using pixelMember
    · have horizontalEquality := congrArg Prod.fst equality
      have verticalEquality := congrArg Prod.snd equality
      apply Prod.ext
      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin, location] at horizontalEquality ⊢
        nlinarith
      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin, location] at verticalEquality ⊢
        nlinarith

/-- A locally exact and geometrically coherent assignment instantiates the
abstract footprint atlas. -/
def footprintAtlasOfAssignment (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
    FootprintAtlas tromino latticeBlockWindow
      (drawingBlockRegion tromino drawing) where
  footprints := drawingBlockFootprints tromino drawing assignment
  regionInside := by
    intro location
    apply latticeBlockRegion_subset
    simpa only [Gadget.IsWellFormed, orthogonalCellGadget, paperGadget,
      Gadget.window] using
      orthogonalCellGadget_wellFormed tromino (drawing.getAt location)
  windowsCover := latticeBlockWindows_cover
  localTiling := by
    intro location
    have localPlacementTiling :=
      (mem_exactCellTilings_iff tromino (drawing.getAt location)
        (assignment location)).mp (locallyTiled location)
    have localFootprintTiling :=
      localPlacementTiling.isWindowFootprintTiling
    simpa only [drawingBlockRegion, drawingBlockFootprints,
      latticeBlockWindow, latticeBlockRegion, orthogonalCellGadget,
      paperGadget, Gadget.window] using
      localFootprintTiling.translate (latticeBlockOrigin location)
  coherent := coherent

/-- Coherent local exact-cover states glue to a tiling of the complete lifted
gadget carrier. -/
theorem tileable_liftedGadgetCarrier_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
    tromino.Tileable (liftedGadgetCarrier tromino drawing) := by
  let atlas := footprintAtlasOfAssignment tromino drawing assignment
    locallyTiled coherent
  simpa only [liftedGadgetCarrier, FootprintAtlas.carrier] using atlas.tileable

/-- The same gluing result stated for the actual finite `PeriodicRegion`
presentation emitted by gadget substitution. -/
theorem periodicRegion_tileable_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
    tromino.Tileable (drawing.periodicRegion tromino).carrier := by
  have tiling := tileable_liftedGadgetCarrier_of_coherent tromino drawing
    assignment locallyTiled coherent
  rw [liftedGadgetCarrier_eq_expandedCarrier,
    ← PeriodicOrthogonalDrawing.periodicRegion_carrier_eq] at tiling
  exact tiling

/-- The finite-state correctness goal for Figures 11 and 12. -/
def OrientationBehaviorCorrect (tromino : Tromino) : Prop :=
  ∀ drawing : PeriodicOrthogonalDrawing,
    drawing.HasOrientation ↔ HasCompatibleGadgetTiling tromino drawing

/-- The geometric assembly correctness goal for the `6 × 6` substitution. -/
def SubstitutionAssemblyCorrect (tromino : Tromino) : Prop :=
  ∀ drawing : PeriodicOrthogonalDrawing,
    HasCompatibleGadgetTiling tromino drawing ↔
      tromino.Tileable (drawing.periodicRegion tromino).carrier

end Gadget
end LeanTrominoes
