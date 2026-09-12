/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableOriginComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseOriginData
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSourceIndexedClausePositions

/-! # Affine origins of the actual horizontal variable and clause gadgets -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

private theorem scale128_scale2 (point : Cell) :
    Cell.scale 128 (Cell.scale 2 point) = Cell.scale 256 point := by
  rcases point with ⟨x, y⟩
  simp only [Cell.scale]
  apply Prod.ext <;> dsimp only <;> omega

/-- Padding and macrocell scaling multiply each routed variable coordinate
by 256 before the fixed variable-gadget offset. -/
theorem horizontalThreeDMVariableOriginComputed_eq_affine (source : PeriodicCNF Nat) (atom : RoutedVariable) :
    horizontalThreeDMVariableOriginComputed source atom =
      Cell.add (Cell.scale 256 ((horizontalRoutedPlacementComputed source).position atom)) (20, 64) := by
  unfold horizontalThreeDMVariableOriginComputed horizontalPaddedRoutedPositionComputed
  rw [scale128_scale2]

/-- Actual clause-gadget origins, repeated once per normalized literal. -/
def horizontalPresentedClauseGadgetOrigins (source : PeriodicCNF Nat) : List Cell :=
  (horizontalNormalizedRoutedFormulaComputed source).clauses.flatMap fun clause =>
    List.replicate clause.literals.length (Cell.add (Cell.scale 128 clause.position) (50, 60))

/-- Anchor normalization uses each routed clause's canonical position;
padding and macrocell scaling therefore give the same factor 256. -/
theorem horizontalPresentedClauseGadgetOrigins_eq_affine (source : PeriodicCNF Nat) :
    horizontalPresentedClauseGadgetOrigins source =
      (presentedIncidenceClausePositions (horizontalRoutedFormulaComputed source)
        (horizontalRoutedPlacementComputed source)).map
          (fun point => Cell.add (Cell.scale 256 point) (50, 60)) := by
  unfold horizontalPresentedClauseGadgetOrigins
  rw [horizontalNormalizedRoutedFormulaComputed_eq_normalizedSource]
  simp only [PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource,
    PositionedPeriodicCNF.anchorNormalize, PositionedPeriodicCNF.scale_clauses,
    List.flatMap_map, PositionedPeriodicClause.scale_literals,
    PositionedPeriodicCNF.canonicalClausePosition_scale, PeriodicClause.anchorNormalize_length,
    presentedIncidenceClausePositions, List.map_flatMap, List.map_replicate, Nat.cast_ofNat, scale128_scale2]

end LeanTrominoes.PeriodicCNFStripReduction
end
