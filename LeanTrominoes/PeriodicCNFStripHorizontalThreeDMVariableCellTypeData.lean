/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleCellTypeDirections
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData

/-! # Finite local cell-type data for variable triples -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Final normalized cell type read from the three finite local routes of a
variable-module triple. -/
def horizontalVariableTripleCellTypeComputed
    (source : PeriodicCNF Nat) (atom : RoutedVariable)
    (triple : Triple RoutedVariable) : OrthogonalCellType :=
  horizontalTripleCellTypeFromDirections
    (AxisDirection.polylineFirstDirection
      (horizontalVariableIncidenceLocalRouteComputed
        (((source, atom), triple), .red)))
    (AxisDirection.polylineFirstDirection
      (horizontalVariableIncidenceLocalRouteComputed
        (((source, atom), triple), .green)))
    (AxisDirection.polylineFirstDirection
      (horizontalVariableIncidenceLocalRouteComputed
        (((source, atom), triple), .blue)))

/-- Pointwise reduction of the three original incidence directions to local
variable-table directions determines the complete triple cell type. -/
theorem horizontalFinalVariableTripleCellTypeComputed_eq_of_directions
    (source : PeriodicCNF Nat)
    (tripleIndex : Nat) (atom : RoutedVariable)
    (triple : Triple RoutedVariable)
    (indexLt : tripleIndex <
      (horizontalNormalizationInputComputed source).problem.triples.length)
    (directions : ∀ color,
      AxisDirection.polylineFirstDirection
          (PeriodicThreeDM.NormalizationCompiler.incidenceRoute
            (horizontalNormalizationInputComputed source)
            ⟨tripleIndex, color⟩) =
        AxisDirection.polylineFirstDirection
          (horizontalVariableIncidenceLocalRouteComputed
            (((source, atom), triple), color))) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple tripleIndex) =
      horizontalVariableTripleCellTypeComputed source atom triple := by
  rw [horizontalFinalVertexCellType_eq_incidenceDirections
    source tripleIndex indexLt]
  unfold horizontalVariableTripleCellTypeComputed
  rw [directions .red, directions .green, directions .blue]

end PeriodicCNFStripReduction
end LeanTrominoes
