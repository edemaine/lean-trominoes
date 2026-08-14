/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityVariableInput

/-! # Primitive-recursive origin translation of a retained variable route -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

theorem routedVariableRouteTransform_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : RoutedVariableRouteInput Variable × Cell =>
      Cell.add
        (routedVariableOrigin input.1.1.1.1.1
          input.1.1.1.1.2) input.2 := by
  have origin : Primrec fun input : RoutedVariableRouteInput Variable =>
      routedVariableOrigin input.1.1.1.1 input.1.1.1.2 :=
    routedVariableOrigin_primrec.comp
      (Primrec.fst.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  exact Computability.cell_add_primrec.comp
    (origin.comp Primrec.fst) Primrec.snd

end PeriodicOrthocrossing
end LeanTrominoes
