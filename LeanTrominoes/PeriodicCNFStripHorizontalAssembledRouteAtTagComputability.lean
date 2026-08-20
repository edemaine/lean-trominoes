/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteTripleLookupComputability
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceRouteComputability

/-! # Computability of tag-indexed horizontal incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalAssembledRouteAtTagComputed_primrec :
    Primrec horizontalAssembledRouteAtTagComputed := by
  have none : Primrec fun _input :
      PeriodicCNF Nat × PeriodicThreeDM.IncidenceTag =>
      ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun
      (input : PeriodicCNF Nat × PeriodicThreeDM.IncidenceTag)
      (triple : PeriodicPlanarOneInThreeToThreeDM.Triple RoutedVariable) =>
      horizontalTypedIncidenceRouteComputed
        ((input.1, triple), input.2.color) := by
    have routeInput : Primrec₂ fun
        (input : PeriodicCNF Nat × PeriodicThreeDM.IncidenceTag)
        (triple : PeriodicPlanarOneInThreeToThreeDM.Triple RoutedVariable) =>
        ((input.1, triple), input.2.color) := by
      exact Primrec.pair
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (PeriodicThreeDM.IncidenceTag.color_primrec.comp
          (Primrec.snd.comp Primrec.fst))
    exact horizontalTypedIncidenceRouteComputed_primrec.comp routeInput
  exact (Primrec.option_casesOn
    horizontalAssembledRouteTriple?Computed_primrec none some).of_eq
      fun input => by
        unfold horizontalAssembledRouteAtTagComputed
          PeriodicPlanarOneInThreeToThreeDM.typedRouteFromOptionData
        cases horizontalAssembledRouteTriple?Computed input <;> rfl

end PeriodicCNFStripReduction
end LeanTrominoes
