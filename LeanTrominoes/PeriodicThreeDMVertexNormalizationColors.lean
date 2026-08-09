import LeanTrominoes.PeriodicThreeDMVertexNormalizationRoutes

/-!
# Color correctness of normalized contracted vertices

The executable normalization code deliberately uses ordinary list matching,
while the geometric proofs use `ContractedVertexFan`.  This module identifies
the two views and verifies the final `OrthogonalCellType` selected at every
retained vertex.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace CanonicalVertexPort

/-- Corresponding side in the normalized drawing-cell interface. -/
def side : CanonicalVertexPort → Side
  | .west => .west
  | .north => .north
  | .east => .east

end CanonicalVertexPort

namespace PeriodicThreeDM

namespace ContractedVertexFan

@[simp]
theorem endpointTripleAt_eq
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex) :
    problem.endpointTripleAt vertex =
      some (fan.first, fan.second, fan.third) := by
  simp [endpointTripleAt, fan.endpoints_eq]

/-- Executable omitted-side selection agrees with the fan certificate. -/
theorem omittedSideAt_eq
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex) :
    omittedSideAt presentation.toPlanarPresentation vertex =
      fan.coloredFan.omitted := by
  unfold omittedSideAt
  rw [fan.endpointTripleAt_eq]
  rfl

/-- Executable old-side color lookup agrees with the fan certificate. -/
theorem endpointColorAtSide_eq
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex)
    (side : VertexSide) :
    endpointColorAtSide presentation.toPlanarPresentation vertex side =
      fan.coloredFan.colorAtSide side := by
  unfold endpointColorAtSide
  rw [fan.endpointTripleAt_eq]
  rfl

/-- Hence the executable canonical coloring is exactly the coloring already
proved correct for the finite fan. -/
theorem canonicalColoringAt_eq
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    {vertex : PeriodicThreeDMVertex}
    (fan : ContractedVertexFan presentation vertex) :
    canonicalColoringAt presentation.toPlanarPresentation vertex =
      fan.coloredFan.canonicalColoring := by
  funext port
  simp [canonicalColoringAt, fan.omittedSideAt_eq,
    fan.endpointColorAtSide_eq, ColoredFan.canonicalColoring]

end ContractedVertexFan

/-- The executable canonical coloring at an indexed triple is a permutation
of RGB. -/
theorem canonicalColoringAt_nodup_triple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    let coloring := canonicalColoringAt
      presentation.toPlanarPresentation (.triple tripleIndex)
    [coloring .west, coloring .north, coloring .east].Nodup := by
  rcases exists_contractVertexFan_at_triple presentation wellFormed degree
      tripleIndex indexLt with ⟨fan⟩
  rw [fan.canonicalColoringAt_eq]
  exact fan.coloredFan.canonicalColoring_nodup
    (fan.colors_nodup_of_triple degree tripleIndex)

/-- The executable canonical coloring at a retained element is constant. -/
theorem canonicalColoringAt_eq_element_color
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degreeTwoOrThree : problem.DegreeTwoOrThree)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3) :
    canonicalColoringAt presentation.toPlanarPresentation
        (.element color atom) =
      fun _ => color := by
  rcases exists_contractVertexFan_at_element presentation degreeTwoOrThree
      color atom atomLt degreeThree with ⟨fan⟩
  rw [fan.canonicalColoringAt_eq]
  exact fan.coloredFan_eq_monochromatic color atom

/-- The selected final trichromatic cell has exactly the normalized colors
on west, north, and east, with no south port. -/
theorem PlanarPresentation.finalVertexCellType_portColors_triple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length) :
    let coloring := canonicalColoringAt
      presentation.toPlanarPresentation (.triple tripleIndex)
    let normalized := normalizeTrichromaticColoring coloring
    let cellType := presentation.toPlanarPresentation.finalVertexCellType
      (.triple tripleIndex)
    cellType.portColor .west = some (normalized .west) ∧
      cellType.portColor .north = some (normalized .north) ∧
      cellType.portColor .east = some (normalized .east) ∧
      cellType.portColor .south = none := by
  have nodup := canonicalColoringAt_nodup_triple presentation wellFormed
    degree tripleIndex indexLt
  simpa [PlanarPresentation.finalVertexCellType] using
    trichromaticVertex_portColors
      (canonicalColoringAt presentation.toPlanarPresentation
        (.triple tripleIndex)) nodup

/-- The selected final monochromatic cell exposes the element color on its
three canonical ports and no south port. -/
theorem PlanarPresentation.finalVertexCellType_portColors_element
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat) :
    let cellType := presentation.finalVertexCellType
      (.element color atom)
    cellType.portColor .west = some color ∧
      cellType.portColor .north = some color ∧
      cellType.portColor .east = some color ∧
      cellType.portColor .south = none := by
  simpa [PlanarPresentation.finalVertexCellType] using
    monochromaticVertex_portColors color

end PeriodicThreeDM
end LeanTrominoes
