/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalPaddedRoutedPlacementPositionComputability

/-! # Executable variable origins of the horizontal 3DM assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Origin of the fixed variable gadget inside its `128 × 128` macrocell. -/
def horizontalThreeDMVariableOriginComputed
    (source : PeriodicCNF Nat) (atom : RoutedVariable) : Cell :=
  Cell.add
    (Cell.scale 128
      (horizontalPaddedRoutedPositionComputed source atom))
    (20, 64)

theorem horizontalThreeDMVariableOriginComputed_primrec :
    Primrec fun input : PeriodicCNF Nat × RoutedVariable =>
      horizontalThreeDMVariableOriginComputed input.1 input.2 := by
  have scaled : Primrec fun input : PeriodicCNF Nat × RoutedVariable =>
      Cell.scale 128
        (horizontalPaddedRoutedPositionComputed input.1 input.2) :=
    Computability.cell_scale_primrec.comp
      (Primrec.const (128 : Int))
      horizontalPaddedRoutedPositionComputed_primrec
  exact
    (Computability.cell_add_primrec.comp scaled
      (Primrec.const ((20, 64) : Cell))).of_eq fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
