/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DegreeThreeVertexNormalizationTemplates
import LeanTrominoes.OrthogonalDrawing

/-!
# Port bookkeeping for degree-three normalization

The finite templates preserve cyclic order.  This module supplies their
discrete bookkeeping: invert the omitted-side template, track one clockwise
rotation, choose zero, one, or two rotations to put red at the north port,
and recover the corresponding trichromatic cell order.
-/

namespace LeanTrominoes
namespace DegreeThreeVertexNormalization

open Gadget

/-- Canonical port connected to a used old side by the first Figure 2
normalization template.  The value on the omitted side is an unused total
fallback. -/
def canonicalPortForSide
    (omitted : VertexSide) : VertexSide → CanonicalVertexPort
  | side =>
      match omitted, side with
      | .north, .south => .west
      | .north, .west => .north
      | .north, .east => .east
      | .east, .west => .west
      | .east, .north => .north
      | .east, .south => .east
      | .south, .west => .west
      | .south, .north => .north
      | .south, .east => .east
      | .west, .south => .west
      | .west, .north => .north
      | .west, .east => .east
      | _, _ => .west

/-- On every side actually used by the old drawing, port lookup is the
inverse of the first normalization template's boundary permutation. -/
theorem boundarySide_canonicalPortForSide
    (omitted side : VertexSide) (used : side ≠ omitted) :
    boundarySide omitted (canonicalPortForSide omitted side) = side := by
  cases omitted <;> cases side <;> simp_all [canonicalPortForSide, boundarySide]

/-- Conversely, every canonical port is recovered from its boundary side. -/
theorem canonicalPortForSide_boundarySide
    (omitted : VertexSide) (port : CanonicalVertexPort) :
    canonicalPortForSide omitted (boundarySide omitted port) = port := by
  cases omitted <;> cases port <;> rfl

/-- Number of clockwise cyclic port-rotation templates to apply. -/
inductive PortRotationCount
  | zero
  | one
  | two
  deriving DecidableEq, Fintype, Repr

/-- One clockwise template connects each new port to this old port. -/
def oldPortAfterClockwise : CanonicalVertexPort → CanonicalVertexPort
  | .west => .east
  | .north => .west
  | .east => .north

/-- Old port reached by a new port after zero, one, or two clockwise
templates. -/
def oldPortAfterRotations :
    PortRotationCount → CanonicalVertexPort → CanonicalVertexPort
  | .zero, port => port
  | .one, port => oldPortAfterClockwise port
  | .two, port => oldPortAfterClockwise (oldPortAfterClockwise port)

/-- Transport a coloring through the selected cyclic rotation templates. -/
def rotateColoring (count : PortRotationCount)
    (coloring : CanonicalVertexPort → WireColor) :
    CanonicalVertexPort → WireColor :=
  fun port => coloring (oldPortAfterRotations count port)

/-- Unique rotation count that moves a specified current port to the new
north port. -/
def rotationsToNorth : CanonicalVertexPort → PortRotationCount
  | .west => .one
  | .north => .zero
  | .east => .two

/-- The selected count really makes the old specified port feed the new
north port. -/
theorem oldPortAfterRotations_north_rotationsToNorth
    (port : CanonicalVertexPort) :
    oldPortAfterRotations (rotationsToNorth port) .north = port := by
  cases port <;> rfl

/-- The current port carrying a requested color, with north as a total
fallback for malformed colorings. -/
def portOfColor (coloring : CanonicalVertexPort → WireColor)
    (wanted : WireColor) : CanonicalVertexPort :=
  if coloring .west = wanted then .west
  else if coloring .north = wanted then .north
  else if coloring .east = wanted then .east
  else .north

/-- A color present on one of the three ports is recovered by lookup. -/
theorem coloring_portOfColor
    (coloring : CanonicalVertexPort → WireColor)
    (wanted : WireColor)
    (present : wanted ∈ [coloring .west, coloring .north, coloring .east]) :
    coloring (portOfColor coloring wanted) = wanted := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  by_cases west : coloring .west = wanted
  · simp [portOfColor, west]
  by_cases north : coloring .north = wanted
  · simp [portOfColor, west, north]
  rcases present with present | present | present
  · exact (west present.symm).elim
  · exact (north present.symm).elim
  · have westEast : coloring .west ≠ coloring .east := by
      intro same
      exact west (same.trans present.symm)
    have northEast : coloring .north ≠ coloring .east := by
      intro same
      exact north (same.trans present.symm)
    simp [portOfColor, present, westEast, northEast]

/-- Rotate a trichromatic port assignment until red occupies north. -/
def normalizeTrichromaticColoring
    (coloring : CanonicalVertexPort → WireColor) :
    CanonicalVertexPort → WireColor :=
  rotateColoring
    (rotationsToNorth (portOfColor coloring .red)) coloring

/-- Choose the normalized vertex cell's left-to-right color order. -/
def trichromaticOrder
    (coloring : CanonicalVertexPort → WireColor) : TrichromaticOrder :=
  if normalizeTrichromaticColoring coloring .west = .blue then
    .blueRedGreen
  else
    .greenRedBlue

/-- Pairwise distinct RGB incidences normalize to red at north and the two
remaining colors at west and east. -/
theorem normalizeTrichromaticColoring_shape
    (coloring : CanonicalVertexPort → WireColor)
    (nodup :
      [coloring .west, coloring .north, coloring .east].Nodup) :
    normalizeTrichromaticColoring coloring .north = .red ∧
      ((normalizeTrichromaticColoring coloring .west = .blue ∧
          normalizeTrichromaticColoring coloring .east = .green) ∨
        (normalizeTrichromaticColoring coloring .west = .green ∧
          normalizeTrichromaticColoring coloring .east = .blue)) := by
  revert coloring
  native_decide

/-- The chosen `OrthogonalCellType` exposes exactly the normalized RGB port
colors, with no south port. -/
theorem trichromaticVertex_portColors
    (coloring : CanonicalVertexPort → WireColor)
    (nodup :
      [coloring .west, coloring .north, coloring .east].Nodup) :
    let normalized := normalizeTrichromaticColoring coloring
    let cellType : OrthogonalCellType :=
      .trichromaticVertex (trichromaticOrder coloring)
    cellType.portColor .west = some (normalized .west) ∧
      cellType.portColor .north = some (normalized .north) ∧
      cellType.portColor .east = some (normalized .east) ∧
      cellType.portColor .south = none := by
  revert coloring
  native_decide

/-- A monochromatic normalized vertex exposes its color on west, north, and
east and has no south port. -/
theorem monochromaticVertex_portColors (color : WireColor) :
    let cellType : OrthogonalCellType := .monochromaticVertex color
    cellType.portColor .west = some color ∧
      cellType.portColor .north = some color ∧
      cellType.portColor .east = some color ∧
      cellType.portColor .south = none := by
  cases color <;> native_decide

end DegreeThreeVertexNormalization
end LeanTrominoes
