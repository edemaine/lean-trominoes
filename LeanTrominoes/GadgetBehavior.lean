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
