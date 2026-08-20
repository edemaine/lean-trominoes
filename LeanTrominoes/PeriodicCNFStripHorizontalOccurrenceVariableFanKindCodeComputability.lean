/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanKindAtComputability

/-! # Computability of variable-fan connector-kind codes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableRibbonKindsCodeComputed_primrec :
    Primrec horizontalOccurrenceVariableRibbonKindsCodeComputed := by
  have encodeAt (slot : VariableSiteSlot) : Primrec fun input :
      HorizontalVariableRibbonFanInput =>
        variableConnectorKindEquivFin
          (horizontalOccurrenceVariableRibbonKindComputed (input, slot)) :=
    horizontalOccurrenceVariableRibbonKindCodeAt_primrec.comp
      (Primrec.pair Primrec.id (Primrec.const slot))
  exact Primrec.pair (encodeAt .first)
    (Primrec.pair (encodeAt .second) (encodeAt .third))

end PeriodicCNFStripReduction
end LeanTrominoes
