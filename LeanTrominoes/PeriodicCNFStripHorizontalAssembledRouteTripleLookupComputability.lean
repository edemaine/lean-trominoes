/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedTriplesComputability
import LeanTrominoes.PeriodicThreeDMNormalizationEncoding

/-! # Computability of tag-indexed horizontal typed-triple lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalAssembledRouteTriple?Computed_primrec :
    Primrec horizontalAssembledRouteTriple?Computed := by
  exact Primrec.list_getElem?.comp
    (horizontalThreeDMTypedTriplesComputed_primrec.comp Primrec.fst)
    (PeriodicThreeDM.IncidenceTag.tripleIndex_primrec.comp Primrec.snd)

end PeriodicCNFStripReduction
end LeanTrominoes
