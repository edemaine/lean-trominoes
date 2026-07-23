import LeanTrominoes.Gadget

/-!
# The finite gadget library for Theorem 5.2

Figures 11 and 12 of the paper give one `6 × 6` region for every local
intersection type in the normalized orthogonal graph drawing.  This file
records those regions as data.  Coordinates have their origin at the
top-left corner of a figure window.

The later correctness proof will derive the possible boundary states by the
verified exact-cover search, rather than copying the pictured solutions.
-/

namespace LeanTrominoes
namespace Gadget

/-- The three edge colors used by planar trichromatic graph orientation. -/
inductive WireColor
  | red
  | green
  | blue
  deriving DecidableEq, Repr

/-- The axis of a straight wire segment. -/
inductive WireAxis
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The two incident sides of a wire bend. -/
inductive WireBend
  | northeast
  | northwest
  | southeast
  | southwest
  deriving DecidableEq, Repr

/-- The two normalized cyclic orders of a trichromatic vertex. -/
inductive TrichromaticOrder
  | blueRedGreen
  | greenRedBlue
  deriving DecidableEq, Repr

/-- Regard a list of paper pixels as a `6 × 6` gadget. -/
def paperGadget (cells : List Cell) : Gadget where
  width := 6
  height := 6
  region := cells.toFinset

/-- A square of the dual grid that does not intersect the drawing contributes
no target cells. -/
def blankGadget : Gadget := paperGadget []

theorem blankGadget_wellFormed : blankGadget.IsWellFormed := by
  native_decide

/-! ## Straight wires -/

/-- Pixel masks for all straight wire gadgets in Figures 11 and 12. -/
def wireCells : Tromino → WireAxis → WireColor → List Cell
  | .L, .horizontal, .red => figure11RedWireCells
  | .L, .horizontal, .green =>
      [(0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2),
        (0, 3), (2, 3), (4, 3)]
  | .L, .horizontal, .blue =>
      [(0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3),
        (1, 4), (3, 4), (5, 4)]
  | .L, .vertical, .red =>
      [(2, 0), (2, 1), (3, 1), (2, 2), (2, 3), (3, 3),
        (2, 4), (2, 5), (3, 5)]
  | .L, .vertical, .green =>
      [(3, 0), (3, 1), (4, 1), (3, 2), (3, 3), (4, 3),
        (3, 4), (3, 5), (4, 5)]
  | .L, .vertical, .blue =>
      [(2, 0), (3, 0), (2, 1), (2, 2), (3, 2), (2, 3),
        (2, 4), (3, 4), (2, 5)]
  | .I, .horizontal, .red => figure12RedWireCells
  | .I, .horizontal, .green =>
      [(2, 1), (3, 1), (4, 1), (5, 1),
        (2, 2), (5, 2), (2, 3), (5, 3),
        (0, 4), (1, 4), (2, 4), (5, 4)]
  | .I, .horizontal, .blue =>
      [(1, 1), (2, 1), (3, 1), (4, 1),
        (1, 2), (4, 2), (1, 3), (4, 3),
        (0, 4), (1, 4), (4, 4), (5, 4)]
  | .I, .vertical, .red =>
      [(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]
  | .I, .vertical, .green =>
      [(2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]
  | .I, .vertical, .blue =>
      [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)]

/-- A straight wire gadget from Figure 11 or 12. -/
def wireGadget (tromino : Tromino) (axis : WireAxis)
    (color : WireColor) : Gadget :=
  paperGadget (wireCells tromino axis color)

theorem wireGadget_wellFormed (tromino : Tromino) (axis : WireAxis)
    (color : WireColor) : (wireGadget tromino axis color).IsWellFormed := by
  cases tromino <;> cases axis <;> cases color <;> native_decide

theorem wireCells_nodup (tromino : Tromino) (axis : WireAxis)
    (color : WireColor) : (wireCells tromino axis color).Nodup := by
  cases tromino <;> cases axis <;> cases color <;> native_decide

theorem figure11RedWire_eq_library :
    figure11RedWire = wireGadget .L .horizontal .red := rfl

theorem figure12RedWire_eq_library :
    figure12RedWire = wireGadget .I .horizontal .red := rfl

/-! ## Wire bends -/

/-- Pixel masks for all wire-bend gadgets in Figures 11 and 12. -/
def bendCells : Tromino → WireBend → WireColor → List Cell
  | .L, .northeast, .red =>
      [(2, 0), (1, 1), (2, 1), (2, 2), (3, 2), (4, 2),
        (5, 2), (3, 3), (5, 3)]
  | .L, .northeast, .green =>
      [(3, 0), (2, 1), (3, 1), (3, 2), (4, 2), (5, 2), (4, 3)]
  | .L, .northeast, .blue =>
      [(1, 0), (2, 0), (2, 1), (1, 2), (2, 2), (2, 3),
        (3, 3), (4, 3), (5, 3), (3, 4), (5, 4)]
  | .L, .northwest, .red =>
      [(2, 0), (2, 1), (3, 1), (0, 2), (1, 2), (2, 2), (1, 3)]
  | .L, .northwest, .green =>
      [(3, 0), (3, 1), (4, 1), (0, 2), (1, 2), (2, 2),
        (3, 2), (0, 3), (2, 3)]
  | .L, .northwest, .blue =>
      [(2, 0), (3, 0), (2, 1), (2, 2), (3, 2),
        (0, 3), (1, 3), (2, 3), (1, 4)]
  | .L, .southeast, .red =>
      [(3, 1), (5, 1), (2, 2), (3, 2), (4, 2), (5, 2),
        (1, 3), (2, 3), (2, 4), (1, 5), (2, 5)]
  | .L, .southeast, .green =>
      [(4, 1), (3, 2), (4, 2), (5, 2), (2, 3), (3, 3),
        (3, 4), (2, 5), (3, 5)]
  | .L, .southeast, .blue =>
      [(3, 2), (5, 2), (2, 3), (3, 3), (4, 3), (5, 3),
        (1, 4), (2, 4), (2, 5)]
  | .L, .southwest, .red =>
      [(1, 1), (0, 2), (1, 2), (2, 2), (2, 3), (3, 3),
        (2, 4), (2, 5), (3, 5)]
  | .L, .southwest, .green =>
      [(0, 1), (2, 1), (0, 2), (1, 2), (2, 2), (3, 2),
        (3, 3), (4, 3), (3, 4), (3, 5), (4, 5)]
  | .L, .southwest, .blue =>
      [(1, 2), (0, 3), (1, 3), (2, 3), (2, 4), (3, 4), (2, 5)]
  | .I, .northeast, .red =>
      [(3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 4), (5, 4)]
  | .I, .northeast, .green =>
      [(2, 0), (2, 1), (2, 2), (2, 3), (2, 4),
        (3, 4), (4, 4), (5, 4)]
  | .I, .northeast, .blue =>
      [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
        (2, 4), (3, 4), (4, 4), (5, 4)]
  | .I, .northwest, .red =>
      [(3, 0), (3, 1), (3, 2), (3, 3),
        (0, 4), (1, 4), (2, 4), (3, 4)]
  | .I, .northwest, .green =>
      [(2, 0), (2, 1), (2, 2), (2, 3), (0, 4), (1, 4), (2, 4)]
  | .I, .northwest, .blue =>
      [(1, 0), (1, 1), (1, 2), (1, 3), (0, 4), (1, 4)]
  | .I, .southeast, .red =>
      [(3, 4), (4, 4), (5, 4), (3, 5)]
  | .I, .southeast, .green =>
      [(2, 4), (3, 4), (4, 4), (5, 4), (2, 5)]
  | .I, .southeast, .blue =>
      [(1, 4), (2, 4), (3, 4), (4, 4), (5, 4), (1, 5)]
  | .I, .southwest, .red =>
      [(0, 4), (1, 4), (2, 4), (3, 4), (3, 5)]
  | .I, .southwest, .green =>
      [(0, 4), (1, 4), (2, 4), (2, 5)]
  | .I, .southwest, .blue =>
      [(0, 4), (1, 4), (1, 5)]

/-- A wire-bend gadget from Figure 11 or 12. -/
def bendGadget (tromino : Tromino) (bend : WireBend)
    (color : WireColor) : Gadget :=
  paperGadget (bendCells tromino bend color)

theorem bendGadget_wellFormed (tromino : Tromino) (bend : WireBend)
    (color : WireColor) : (bendGadget tromino bend color).IsWellFormed := by
  cases tromino <;> cases bend <;> cases color <;> native_decide

theorem bendCells_nodup (tromino : Tromino) (bend : WireBend)
    (color : WireColor) : (bendCells tromino bend color).Nodup := by
  cases tromino <;> cases bend <;> cases color <;> native_decide

/-! ## Degree-three vertices -/

/-- Pixel masks for the monochromatic 1-in-3 vertex gadgets.  Their three
ports are on the west, north, and east sides. -/
def monochromaticVertexCells : Tromino → WireColor → List Cell
  | .L, .red =>
      [(2, 0), (2, 1), (3, 1),
        (0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2),
        (1, 3), (3, 3), (5, 3)]
  | .L, .green =>
      [(3, 0), (3, 1), (4, 1),
        (0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2),
        (0, 3), (2, 3), (4, 3)]
  | .L, .blue =>
      [(2, 0), (3, 0), (2, 1), (2, 2), (3, 2),
        (0, 3), (1, 3), (2, 3), (3, 3), (4, 3), (5, 3),
        (1, 4), (3, 4), (5, 4)]
  | .I, .red =>
      [(3, 0), (3, 1), (3, 2), (3, 3),
        (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4)]
  | .I, .green =>
      [(2, 0), (2, 1), (2, 2), (2, 3),
        (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4)]
  | .I, .blue =>
      [(1, 0), (1, 1), (1, 2), (1, 3),
        (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4)]

/-- A monochromatic 1-in-3 degree-three vertex gadget. -/
def monochromaticVertexGadget (tromino : Tromino)
    (color : WireColor) : Gadget :=
  paperGadget (monochromaticVertexCells tromino color)

theorem monochromaticVertexGadget_wellFormed (tromino : Tromino)
    (color : WireColor) :
    (monochromaticVertexGadget tromino color).IsWellFormed := by
  cases tromino <;> cases color <;> native_decide

theorem monochromaticVertexCells_nodup (tromino : Tromino)
    (color : WireColor) :
    (monochromaticVertexCells tromino color).Nodup := by
  cases tromino <;> cases color <;> native_decide

/-- Pixel masks for the two normalized trichromatic 0-or-3-in-3 vertices.
The order names list the west, north, and east port colors. -/
def trichromaticVertexCells : Tromino → TrichromaticOrder → List Cell
  | .L, .blueRedGreen =>
      [(2, 0), (1, 1), (2, 1),
        (2, 2), (3, 2), (4, 2), (5, 2),
        (0, 3), (1, 3), (2, 3), (4, 3), (1, 4)]
  | .L, .greenRedBlue =>
      [(2, 0), (2, 1), (3, 1),
        (0, 2), (1, 2), (2, 2),
        (0, 3), (2, 3), (3, 3), (4, 3), (5, 3),
        (3, 4), (5, 4)]
  | .I, .blueRedGreen =>
      [(3, 0),
        (1, 1), (2, 1), (3, 1),
        (1, 2), (2, 2), (1, 3), (2, 3),
        (0, 4), (1, 4), (2, 4), (3, 4), (4, 4), (5, 4)]
  | .I, .greenRedBlue =>
      [(3, 0),
        (2, 1), (3, 1), (4, 1),
        (2, 2), (4, 2), (2, 3), (4, 3),
        (0, 4), (1, 4), (2, 4), (4, 4), (5, 4)]

/-- A trichromatic 0-or-3-in-3 degree-three vertex gadget. -/
def trichromaticVertexGadget (tromino : Tromino)
    (order : TrichromaticOrder) : Gadget :=
  paperGadget (trichromaticVertexCells tromino order)

theorem trichromaticVertexGadget_wellFormed (tromino : Tromino)
    (order : TrichromaticOrder) :
    (trichromaticVertexGadget tromino order).IsWellFormed := by
  cases tromino <;> cases order <;> native_decide

theorem trichromaticVertexCells_nodup (tromino : Tromino)
    (order : TrichromaticOrder) :
    (trichromaticVertexCells tromino order).Nodup := by
  cases tromino <;> cases order <;> native_decide

/-! ## Complete local drawing alphabet -/

/-- Every possible way a normalized orthogonal drawing can intersect one
square face of its overlaid grid. -/
inductive OrthogonalCellType
  | blank
  | wire (axis : WireAxis) (color : WireColor)
  | bend (bend : WireBend) (color : WireColor)
  | monochromaticVertex (color : WireColor)
  | trichromaticVertex (order : TrichromaticOrder)
  deriving DecidableEq, Repr

/-- The paper pixels selected by a local drawing cell. -/
def orthogonalCellPixels (tromino : Tromino) : OrthogonalCellType → List Cell
  | .blank => []
  | .wire axis color => wireCells tromino axis color
  | .bend bend color => bendCells tromino bend color
  | .monochromaticVertex color => monochromaticVertexCells tromino color
  | .trichromaticVertex order => trichromaticVertexCells tromino order

/-- Compile one local drawing cell to its Figure 11 or 12 gadget. -/
def orthogonalCellGadget (tromino : Tromino)
    (cellType : OrthogonalCellType) : Gadget :=
  paperGadget (orthogonalCellPixels tromino cellType)

theorem orthogonalCellPixels_nodup (tromino : Tromino)
    (cellType : OrthogonalCellType) :
    (orthogonalCellPixels tromino cellType).Nodup := by
  cases cellType with
  | blank => exact List.nodup_nil
  | wire axis color => exact wireCells_nodup tromino axis color
  | bend bend color => exact bendCells_nodup tromino bend color
  | monochromaticVertex color =>
      exact monochromaticVertexCells_nodup tromino color
  | trichromaticVertex order =>
      exact trichromaticVertexCells_nodup tromino order

theorem orthogonalCellGadget_wellFormed (tromino : Tromino)
    (cellType : OrthogonalCellType) :
    (orthogonalCellGadget tromino cellType).IsWellFormed := by
  cases cellType with
  | blank => exact blankGadget_wellFormed
  | wire axis color => exact wireGadget_wellFormed tromino axis color
  | bend bend color => exact bendGadget_wellFormed tromino bend color
  | monochromaticVertex color =>
      exact monochromaticVertexGadget_wellFormed tromino color
  | trichromaticVertex order =>
      exact trichromaticVertexGadget_wellFormed tromino order

end Gadget
end LeanTrominoes
