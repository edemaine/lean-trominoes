/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMProblemComputability
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability

/-! # Computability of horizontal 3DM incidence tags -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalThreeDMIncidenceTagsComputed_primrec :
    Primrec horizontalThreeDMIncidenceTagsComputed := by
  exact PeriodicThreeDM.NormalizationCompiler.incidenceTags_primrec.comp
    horizontalThreeDMProblemComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
