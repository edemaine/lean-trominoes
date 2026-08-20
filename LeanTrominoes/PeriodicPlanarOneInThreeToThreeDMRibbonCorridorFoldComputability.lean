/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorStepComputability

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- The proof-free right fold implementing a colored corridor is primitive
recursive. -/
theorem ribbonCorridorCoreComputed_primrec :
    Primrec
      (fun input : WireColor × List Cell =>
        ribbonCorridorCoreComputed input.1 input.2) := by
  have packed : Primrec fun combined :
      (WireColor × List Cell) × (Cell × List Cell × List Cell) =>
      (((combined.1.1, combined.2.1),
        (combined.2.2.1, combined.2.2.2)) :
        RibbonCorridorCoreStepInput) :=
    Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have step : Primrec₂ fun
      (input : WireColor × List Cell)
      (state : Cell × List Cell × List Cell) =>
      ribbonCorridorCoreStep
        ((input.1, state.1), (state.2.1, state.2.2)) :=
    (ribbonCorridorCoreStep_primrec.comp packed).to₂
  exact (Primrec.list_rec
    (f := fun input : WireColor × List Cell => input.2)
    (g := fun _ => ([] : List Cell))
    (h := fun input state =>
      ribbonCorridorCoreStep
        ((input.1, state.1), (state.2.1, state.2.2)))
    Primrec.snd (Primrec.const []) step).of_eq fun input => by
      rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
