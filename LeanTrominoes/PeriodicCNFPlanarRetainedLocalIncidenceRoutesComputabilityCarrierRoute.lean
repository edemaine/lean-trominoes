/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityCarrierLens

/-! # Primitive-recursive retained carrier and translated-corner routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PeriodicOrthocrossing

def carrierRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : CarrierRouteInput Variable) : List Cell :=
  carrierLensRoute
    (((PeriodicCNF.incidenceGraph input.1.1.1,
      input.1.1.2), input.1.2), input.2)

theorem carrierRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (carrierRoute (Variable := Variable)) := by
  exact (carrierLensRoute_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (PeriodicCNF.incidenceGraph_primrec.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.fst))
      Primrec.snd)).of_eq
        fun _ => rfl

abbrev TranslatedCornerRouteInput :=
  Cell × (((CornerPort × CornerPort) × Nat) × Nat)


end PeriodicOrthocrossing
end LeanTrominoes
