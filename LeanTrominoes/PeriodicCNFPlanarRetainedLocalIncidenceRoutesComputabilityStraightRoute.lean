/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityDatatypes
import LeanTrominoes.EmbeddedCNFIncidenceDrawing

/-! # Primitive-recursive two-point local incidence routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PlanarThreeSAT

theorem straightIncidenceRoute_primrec :
    Primrec₂ straightIncidenceRoute := by
  change Primrec fun input : Cell × Cell => [input.1, input.2]
  exact Primrec.list_cons.comp Primrec.fst
    (Primrec.list_cons.comp Primrec.snd (Primrec.const []))


end PlanarThreeSAT
end LeanTrominoes
