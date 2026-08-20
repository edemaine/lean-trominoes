/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseComputability

/-! # Computability of the horizontal occurrence route query -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalOccurrenceRouteQueryInput_primrec :
    Primrec horizontalOccurrenceRouteQueryInput := by
  have clauseIndex : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have literalIndex : Primrec fun input : HorizontalOccurrenceRouteSomeInput =>
      input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair
    (Primrec.pair horizontalOccurrenceRouteSomeSource_primrec clauseIndex)
    literalIndex

end PeriodicCNFStripReduction
end LeanTrominoes
