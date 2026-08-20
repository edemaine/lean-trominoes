/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData

/-! # Computability of ordinary typed-incidence route inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalOrdinaryTypedIncidenceSourceAtomComputed_primrec :
    Primrec horizontalOrdinaryTypedIncidenceSourceAtomComputed := by
  exact Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))

theorem horizontalOrdinaryTypedIncidenceMetadataComputed_primrec :
    Primrec horizontalOrdinaryTypedIncidenceMetadataComputed := by
  exact Primrec.pair
    horizontalOrdinaryTypedIncidenceSourceAtomComputed_primrec
    (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))

theorem horizontalOrdinaryTypedIncidenceRouteInputComputed_primrec :
    Primrec horizontalOrdinaryTypedIncidenceRouteInputComputed := by
  exact Primrec.pair
    (Primrec.pair
      horizontalOrdinaryTypedIncidenceMetadataComputed_primrec
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    (Primrec.snd.comp Primrec.fst)

end PeriodicCNFStripReduction
end LeanTrominoes
