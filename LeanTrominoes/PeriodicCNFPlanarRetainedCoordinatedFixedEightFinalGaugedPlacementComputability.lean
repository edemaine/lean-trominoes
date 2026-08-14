/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDMComputability

/-! # Computability of the retained final gauged placement -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance finalGaugedPlacementComputabilityVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_period_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun source : PeriodicCNF Variable =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        source).period :=
  retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_primrec.of_eq
    fun _ => rfl

theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement_position_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable) =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
        input.1).position input.2 := by
  let Query := PeriodicCNF Variable ×
    OneInThreeNoUnitVariable
      (PeriodicPlanarOneInThreeThreeRawVariable Variable)
  have rawPosition : Primrec fun input : Query =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        input.1).position input.2 :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_position_primrec
  have rawPeriod : Primrec fun input : Query =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        input.1).period :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_primrec.comp
      Primrec.fst
  have gauge : Primrec fun input : Query =>
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        input.1 input.2 :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_primrec
  have translatedGauge : Primrec fun input : Query =>
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        input.1).translation
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
            input.1 input.2) :=
    (Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp rawPeriod) gauge).of_eq
        fun _ => rfl
  exact (Computability.cell_sub_primrec.comp
    rawPosition translatedGauge).of_eq fun _ => rfl

end PeriodicOrthocrossing
end LeanTrominoes
