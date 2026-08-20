/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanLookupComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteComputability

/-! # Computability of finite variable-fan directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance : Inhabited AxisDirection := ⟨.north⟩

theorem horizontalOccurrenceVariableRibbonDirectionComputed_primrec :
    Primrec fun input :
        HorizontalVariableRibbonFanInput × VariableSiteSlot =>
      horizontalOccurrenceVariableRibbonDirectionComputed
        input.1 input.2 := by
  let Input := HorizontalVariableRibbonFanInput × VariableSiteSlot
  have active : Primrec fun input : Input =>
      (horizontalOccurrenceVariableRibbonLookupComputed input).isSome :=
    Primrec.option_isSome.comp
      horizontalOccurrenceVariableRibbonLookupComputed_primrec
  have selectedDirection : Primrec horizontalOccurrenceVariableRibbonDirectionSelect :=
    Computability.finiteDomain_primrec _
  exact selectedDirection.comp
    (Primrec.pair active
      (horizontalOccurrenceSourceVariableDirectionComputed_primrec.comp
        horizontalOccurrenceVariableRibbonRouteInput_primrec))

end PeriodicCNFStripReduction
end LeanTrominoes
