/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData

/-! # Finite direction words of horizontal typed incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Finite variable-site incidence word before its global translation. -/
def horizontalVariableIncidencePrefixDirections
    (input : HorizontalVariableIncidencePrefixInput) :
    List AxisDirection :=
  unitSubdivisionDirections
    (horizontalVariableIncidenceLocalRouteComputed input)

/-- Finite clause-core incidence word before its global translation. -/
def horizontalClauseIncidenceDirections
    (input : X3CClauseSet × WireColor) : List AxisDirection :=
  unitSubdivisionDirections
    (PlanarThreeDM.X3CClauseOrthogonal.route input.1 input.2)

/-- Translating a finite variable-site route to its global module does not
change its direction word. -/
theorem unitSubdivisionDirections_horizontalVariableIncidencePrefixComputed
    (input : HorizontalVariableIncidencePrefixInput) :
    unitSubdivisionDirections
        (horizontalVariableIncidencePrefixComputed input) =
      horizontalVariableIncidencePrefixDirections input := by
  simpa only [horizontalVariableIncidencePrefixComputed,
    horizontalVariableIncidencePrefixDirections] using
    unitSubdivisionDirections_translatePolyline
      (horizontalVariableIncidenceOriginComputed input)
      (horizontalVariableIncidenceLocalRouteComputed input)

/-- Translating a finite clause-core route to its clause module does not
change its direction word. -/
theorem unitSubdivisionDirections_horizontalClauseIncidenceRouteComputed
    (input : HorizontalClauseIncidenceRouteInput) :
    unitSubdivisionDirections
        (horizontalClauseIncidenceRouteComputed input) =
      horizontalClauseIncidenceDirections (input.1.2, input.2) := by
  simpa only [horizontalClauseIncidenceRouteComputed,
    horizontalClauseIncidenceDirections] using
    unitSubdivisionDirections_translatePolyline
      (horizontalThreeDMClauseOriginComputed input.1.1.1 input.1.1.2)
      (PlanarThreeDM.X3CClauseOrthogonal.route input.1.2 input.2)

end PeriodicCNFStripReduction
end LeanTrominoes

end
