/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderExactOperationSemantics
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalDirectionNonempty

/-! # Finite first directions before polarity normalization -/

namespace LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeader
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine PeriodicOrthocrossing

/-- The finite local connector determines the source route's first step. -/
def sourceFirstDirection (header : Header) : AxisDirection :=
  (sourceBlock header []).directions.headD .invalid

/-- A dynamic inherited suffix cannot change the first direction because
every finite local connector has at least one edge. -/
theorem sourceBlock_directions_head (header : Header) (tail : List AxisDirection) :
    (sourceBlock header tail).directions.head? = some (sourceFirstDirection header) := by
  rcases header with ⟨polarity, routePrefix⟩
  cases routePrefix with
  | «local» query =>
      obtain ⟨first, rest, directionsEq⟩ := List.exists_cons_of_ne_nil (normalizedLocalDirectionBlock_ne_nil query)
      simp [sourceFirstDirection, sourceBlock, RetainedFigureNineRouteDirectionBlock.directions, directionsEq]
  | inherited slot query =>
      obtain ⟨first, rest, directionsEq⟩ := List.exists_cons_of_ne_nil (normalizedLocalExtendedDirectionBlock_ne_nil query)
      simp [sourceFirstDirection, sourceBlock, RetainedFigureNineRouteDirectionBlock.directions, directionsEq]

end LeanTrominoes.PeriodicCNFStripReduction.HorizontalRoutedRouteHeader
