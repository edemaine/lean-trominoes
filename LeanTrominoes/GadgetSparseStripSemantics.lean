/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseStripMotif

/-! # Sparse strip-substitution semantics -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- The sparse and complete-raster strip presentations have the same
infinite carrier. -/
theorem ContinuousPlanarPresentation.sparsePeriodicStrip_carrier_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside : presentation.toPlanarPresentation.drawing
      |>.RoutePointsInExpandedVerticalBand)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple : ∀ route ∈ presentation.drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route)
    (tromino : Tromino) :
    (presentation.sparsePeriodicStrip tromino).carrier =
      (presentation.toPlanarPresentation
        |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino).carrier := by
  let dense := presentation.toPlanarPresentation
    |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino
  ext cell
  rw [PeriodicStrip.mem_carrier_iff, PeriodicStrip.mem_carrier_iff]
  change
    (0 ≤ cell.2 ∧ cell.2 < (dense.width : Int) ∧
      ∃ base ∈ (presentation.sparsePeriodicStrip tromino).motif,
        base.2 = cell.2 ∧ (dense.period : Int) ∣ cell.1 - base.1) ↔ _
  constructor
  · rintro ⟨nonnegative, bounded, base, baseMember, row, congruent⟩
    exact ⟨nonnegative, bounded, base,
      (presentation.mem_sparsePeriodicStrip_motif_iff wellFormed degree
        horizontal sourceInside separated sourceSimple tromino base).mp
          baseMember,
      row, congruent⟩
  · rintro ⟨nonnegative, bounded, base, baseMember, row, congruent⟩
    exact ⟨nonnegative, bounded, base,
      (presentation.mem_sparsePeriodicStrip_motif_iff wellFormed degree
        horizontal sourceInside separated sourceSimple tromino base).mpr
          baseMember,
      row, congruent⟩

/-- Sparse assignment-order substitution is a valid strip presentation. -/
theorem ContinuousPlanarPresentation.sparsePeriodicStrip_isWellFormed
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside : presentation.toPlanarPresentation.drawing
      |>.RoutePointsInExpandedVerticalBand)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple : ∀ route ∈ presentation.drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route)
    (tromino : Tromino) :
    (presentation.sparsePeriodicStrip tromino).IsWellFormed := by
  let drawing := presentation.toPlanarPresentation
    |>.stripNormalizedOrthogonalDrawing
  have denseWellFormed := drawing.periodicStrip_isWellFormed tromino
  refine ⟨denseWellFormed.1, denseWellFormed.2.1, ?_⟩
  intro cell member
  have denseMember : cell ∈ (drawing.periodicStrip tromino).motif :=
    (presentation.mem_sparsePeriodicStrip_motif_iff wellFormed degree
      horizontal sourceInside separated sourceSimple tromino cell).mp member
  rw [presentation.sparsePeriodicStrip_inFundamentalDomain_iff tromino cell]
  exact denseWellFormed.2.2 cell denseMember

/-- Sparse assignment order preserves the tromino tiling predicate exactly. -/
theorem ContinuousPlanarPresentation.sparsePeriodicStrip_tiling_iff
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside : presentation.toPlanarPresentation.drawing
      |>.RoutePointsInExpandedVerticalBand)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple : ∀ route ∈ presentation.drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route)
    (tromino : Tromino) :
    PeriodicStripTrominoTiling tromino
        (presentation.sparsePeriodicStrip tromino) ↔
      PeriodicStripTrominoTiling tromino
        (presentation.toPlanarPresentation
          |>.stripNormalizedOrthogonalDrawing.periodicStrip tromino) := by
  unfold PeriodicStripTrominoTiling
  rw [presentation.sparsePeriodicStrip_carrier_eq wellFormed degree
    horizontal sourceInside separated sourceSimple tromino]
  constructor
  · intro tiled
    exact ⟨(presentation.toPlanarPresentation
      |>.stripNormalizedOrthogonalDrawing.periodicStrip_isWellFormed tromino),
      tiled.2⟩
  · intro tiled
    exact ⟨presentation.sparsePeriodicStrip_isWellFormed wellFormed degree
      horizontal sourceInside separated sourceSimple tromino, tiled.2⟩

end PeriodicThreeDM
end LeanTrominoes
