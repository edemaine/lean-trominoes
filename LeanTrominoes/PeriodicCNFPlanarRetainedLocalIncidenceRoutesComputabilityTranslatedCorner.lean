/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityCarrierRoute

/-! # Primitive-recursive translated retained corner routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PeriodicOrthocrossing

def translatedCornerRoute
    (input : TranslatedCornerRouteInput) : List Cell :=
  (cornerEqualityRoutes input.2.1.1.1 input.2.1.1.2
    input.2.1.2 input.2.2).map (Cell.add input.1)

set_option maxHeartbeats 4000000 in
theorem translatedCornerRoute_primrec :
    Primrec translatedCornerRoute := by
  change Primrec fun input : TranslatedCornerRouteInput =>
    (cornerEqualityRoutes input.2.1.1.1 input.2.1.1.2
      input.2.1.2 input.2.2).map (Cell.add input.1)
  have transform : Primrec fun input :
      TranslatedCornerRouteInput × Cell =>
      Cell.add input.1.1 input.2 :=
    Computability.cell_add_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      Primrec.snd
  exact Primrec.list_map
    (cornerEqualityRoutes_primrec.comp Primrec.snd) transform.to₂




end PeriodicOrthocrossing
end LeanTrominoes
