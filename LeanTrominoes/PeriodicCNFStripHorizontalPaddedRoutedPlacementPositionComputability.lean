/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementPositionComputability

/-! # Pointwise doubled placement used by the horizontal 3DM assembly -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Position of a routed variable after the padding scale. -/
def horizontalPaddedRoutedPositionComputed
    (source : PeriodicCNF Nat) (atom : RoutedVariable) : Cell :=
  Cell.scale 2
    ((horizontalRoutedPlacementComputed source).position atom)

theorem horizontalPaddedRoutedPositionComputed_primrec :
    Primrec fun input : PeriodicCNF Nat × RoutedVariable =>
      horizontalPaddedRoutedPositionComputed input.1 input.2 := by
  exact
    (Computability.cell_scale_primrec.comp
      (Primrec.const (2 : Int))
      horizontalRoutedPlacementComputed_position_primrec).of_eq
        fun _ => rfl

end PeriodicCNFStripReduction
end LeanTrominoes
