/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData

/-! # Computability of fixed-red typed-incidence route inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalFixedRedTypedIncidenceRouteInputComputed_primrec :
    Primrec horizontalFixedRedTypedIncidenceRouteInputComputed := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.snd.comp Primrec.fst)

end PeriodicCNFStripReduction
end LeanTrominoes
